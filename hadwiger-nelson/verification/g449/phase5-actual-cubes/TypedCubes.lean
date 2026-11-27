import NormalizeColour
import FourColourCNF

namespace CertifiedG449Rotation

open G449FiniteCoverage

inductive CubeLit where
  | pos (v : Nat) (col : Fin 4)
  | neg (v : Nat) (col : Fin 4)

def CubeLit.holds (f : Nat → Fin 4) : CubeLit → Prop
  | .pos v col => f v = col
  | .neg v col => f v ≠ col

def CubeLit.dimacs : CubeLit → Int
  | .pos v col => CertifiedG449.var v col
  | .neg v col => -(CertifiedG449.var v col : Int)

def request (c i : Nat) : Nat := (rule.getD c []).getD i 3

def cubeAt (c i : Nat) : List CubeLit :=
  if request c i = 3 then []
  else if request c i = 4 then [.neg (slot i) 1]
  else [.pos (slot i) (Fin.ofNat 4 (request c i+1))]

/-- One center unit, followed in order by the seven rule slots.
A free slot contributes no unit; '-' contributes a negative colour-1 unit. -/
def typedCube (c : Nat) : List CubeLit :=
  .pos center 0 :: (List.range 7).flatMap (cubeAt c)

def cubeDIMACSUnits (c : Nat) : List (List Int) :=
  (typedCube c).map fun l => [l.dimacs]

private theorem requested_values_checked :
    (List.range 6).all (fun c => (List.range 7).all (fun i => decide (request c i < 5))) = true := by
  decide +kernel

theorem request_lt (c i : Nat) (hc : c < 6) (hi : i < 7) : request c i < 5 :=
  decide_eq_true_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp requested_values_checked c (List.mem_range.mpr hc))
    i (List.mem_range.mpr hi))

theorem cubeLit_holds_iff_dimacs (f : Nat → Fin 4) (l : CubeLit) :
    l.holds f ↔ CertifiedG449.litSat (CertifiedG449.assignment f) l.dimacs := by
  cases l with
  | pos v c =>
    change f v = c ↔ CertifiedG449.litSat (CertifiedG449.assignment f) (CertifiedG449.var v c : Int)
    rw [CertifiedG449.litSat_pos_var,CertifiedG449.assignment_exact]
  | neg v c =>
    change f v ≠ c ↔ CertifiedG449.litSat (CertifiedG449.assignment f) (-(CertifiedG449.var v c : Int))
    rw [CertifiedG449.litSat_neg_var]
    constructor
    · intro h
      cases e : CertifiedG449.assignment f (CertifiedG449.var v c) with
      | false => rfl
      | true => exact False.elim (h ((CertifiedG449.assignment_exact f v c).mp e))
    · intro h he
      have he' := (CertifiedG449.assignment_exact f v c).mpr he
      rw [h] at he'
      contradiction

theorem typedCube_holds_of_allowed (f : Nat → Fin 4) (hf : properGraph f)
    (hz : f center = 0) (c : Nat) (hc : c < 6) (h : allowed c (colourWord f) = true) :
    ∀ l ∈ typedCube c, l.holds f := by
  have hasMatch : isMatch c (colourWord f) = true := (Bool.and_eq_true_iff.mp h).1
  intro l hl
  unfold typedCube at hl
  rcases List.mem_cons.mp hl with s | rest
  · subst l
    exact hz
  obtain ⟨i,hi,hli⟩ := List.mem_flatMap.mp rest
  have ib := List.mem_range.mp hi
  have q := List.all_eq_true.mp hasMatch i hi
  change (if request c i == 3 then true else
    if request c i == 4 then label (colourWord f) i != 0 else label (colourWord f) i == request c i) = true at q
  rw [colourWord_digit f i ib] at q
  have nz := proper_near_center_ne_zero f hf hz i ib
  by_cases h3 : request c i = 3
  · simp [cubeAt,h3] at hli
  by_cases h4 : request c i = 4
  · have hh : l = CubeLit.neg (slot i) 1 := by simpa [cubeAt,h3,h4] using hli
    subst l
    change f (slot i) ≠ 1
    intro eq
    simp [h3,h4,colDigit,eq] at q
  · have hh : l = CubeLit.pos (slot i) (Fin.ofNat 4 (request c i+1)) := by
      simpa [cubeAt,h3,h4] using hli
    subst l
    change f (slot i) = Fin.ofNat 4 (request c i+1)
    have hh : colDigit f i = request c i := by simpa [h3,h4] using q
    have hr := request_lt c i hc ib
    have hd : (f (slot i)).val ≠ 0 := by
      intro e
      apply nz
      exact Fin.ext e
    have hlt : request c i+1 < 4 := by omega
    apply Fin.ext
    change (f (slot i)).val = (request c i+1)%4
    rw [Nat.mod_eq_of_lt hlt]
    unfold colDigit at hh
    omega

/-- A normalized proper colouring satisfies the actual numbered unit clauses
of one of the six cases, as well as excluding that case's forbidden words. -/
theorem proper_hits_typed_cube (f : Nat → Fin 4) (hf : properGraph f) :
    ∃ c r, c < 6 ∧ r < 7 ∧ ∃ p : Fin 6,
      properGraph (normalize f r p) ∧ normalize f r p center = 0 ∧
      allowed c (colourWord (normalize f r p)) = true ∧
      (∀ l ∈ typedCube c, l.holds (normalize f r p)) ∧
      CertifiedG449.sat (CertifiedG449.assignment (normalize f r p)) (cubeDIMACSUnits c) := by
  obtain ⟨c,r,hc,hr,p,hf',hz,ha⟩ := proper_can_normalize f hf
  have h := typedCube_holds_of_allowed _ hf' hz c hc ha
  refine ⟨c,r,hc,hr,p,hf',hz,ha,h,?_⟩
  intro clause hm
  obtain ⟨lit,hmem,heq⟩ := List.mem_map.mp hm
  subst clause
  exact ⟨lit.dimacs,by simp,(cubeLit_holds_iff_dimacs _ lit).mp (h lit hmem)⟩


/-- Auditable numerical forms of the six upstream cubes (singleton clauses). -/
theorem numbered_cubes_exact :
    (List.range 6).map cubeDIMACSUnits = [[[913], [38], [694], [682], [1606], [726], [750], [1642]], [[913], [38], [694], [682], [1607]], [[913], [38], [694], [683], [1606], [-1642]], [[913], [38], [694], [683], [-1606], [726], [-750], [-1642]], [[913], [38], [694], [683], [-1606], [-726], [750], [-1642]], [[913], [38], [695], [682], [-1606], [726], [-750], [-1642]]] := by decide +kernel

#print axioms numbered_cubes_exact

#print axioms typedCube_holds_of_allowed
#print axioms proper_hits_typed_cube
end CertifiedG449Rotation
