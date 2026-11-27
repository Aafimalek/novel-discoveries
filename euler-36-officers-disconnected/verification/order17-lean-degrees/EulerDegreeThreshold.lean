import EulerNumbering

namespace LatinGap.PairEncoding
open Finset

/-- The archived order-six encoder computes a label's degree in group 1
for group 0, and in group 0 for each of the other groups. -/
def degreePartner (g : Coord) : Coord := if g = 0 then 1 else 0

theorem degreePartner_ne (g : Coord) : g ≠ degreePartner g := by
  fin_cases g <;> decide

def degreeNeighborPair (g : Coord) (a b : Fin 6) : PairKey 6 :=
  if h : g < degreePartner g then ⟨g, degreePartner g, h, a, b⟩
  else ⟨degreePartner g, g, lt_of_le_of_ne (le_of_not_gt h) (degreePartner_ne g).symm, b, a⟩

/-- IDs in the exact size-17 archived formulas after the first cardinality block. -/
def degreeThresholdNumber (g : Coord) (a : Fin 6) (d : Fin 7) : Nat :=
  9719 + 7 * (6 * g.val + a.val) + d.val

theorem degreeThresholdNumber_bounds (g : Coord) (a : Fin 6) (d : Fin 7) :
    9719 ≤ degreeThresholdNumber g a d ∧ degreeThresholdNumber g a d ≤ 9886 := by
  have g' := g.isLt
  have a' := a.isLt
  have d' := d.isLt
  unfold degreeThresholdNumber
  omega

theorem degreeThresholdNumber_injective (g h : Coord) (a b : Fin 6) (d e : Fin 7)
    (he : degreeThresholdNumber g a d = degreeThresholdNumber h b e) : g = h ∧ a = b ∧ d = e := by
  have g' := g.isLt
  have h' := h.isLt
  have a' := a.isLt
  have b' := b.isLt
  have d' := d.isLt
  have e' := e.isLt
  unfold degreeThresholdNumber at he
  exact ⟨Fin.ext (by omega),Fin.ext (by omega),Fin.ext (by omega)⟩

def literal (id : Nat) (b : Bool) : Int := if b then id else -(id : Int)

theorem literal_spec {id : Nat} (hi : 0 < id) (b : Bool) :
    literal id b ≠ 0 ∧ (literal id b).natAbs = id ∧ decide (0 < literal id b) = b := by
  cases b <;> simp [literal] <;> omega

theorem holds_literal_of_mem {v : Nat → Bool} {xs : List Int} {id : Nat} {b : Bool}
    (hm : literal id b ∈ xs) (hi : 0 < id) (hv : v id = b) :
    NumberedHolds v xs := by
  obtain ⟨hn,habs,hs⟩ := literal_spec hi b
  exact ⟨literal id b,hm,hn,by rw [habs,hs]; exact hv⟩

def patternCount (pat : Fin 6 → Bool) : Nat :=
  (univ.filter fun b => pat b = true).card

/-- The 64 rows are in Python Cartesian-product order, most significant first. -/
def degreePattern (n : Nat) (b : Fin 6) : Bool := n.testBit (5-b.val)

def degreeBlocking (g : Coord) (a : Fin 6) (pat : Fin 6 → Bool) : List Int :=
  List.ofFn fun b : Fin 6 => literal (pairNumber (degreeNeighborPair g a b)) (!(pat b))

def degreeAllowed (minimum : Nat) (g : Coord) (a : Fin 6) (count : Nat) : Prop :=
  minimum ≤ count ∧ (g = 0 ∧ a = 0 → count = minimum)

instance (minimum : Nat) (g : Coord) (a : Fin 6) (count : Nat) :
    Decidable (degreeAllowed minimum g a count) := by unfold degreeAllowed; infer_instance

def thresholdIndices (lo : Nat) : List (Fin 7) :=
  (List.ofFn (fun d : Fin 7 => d)).filter (fun d => decide (lo ≤ d.val))

def degreeRow (minimum : Nat) (g : Coord) (a : Fin 6) (pat : Fin 6 → Bool) : List (List Int) :=
  let block := degreeBlocking g a pat
  let count := patternCount pat
  if degreeAllowed minimum g a count then
    (thresholdIndices minimum).map fun d =>
      block ++ [literal (degreeThresholdNumber g a d) (decide (d.val ≤ count))]
  else [block]

def degreeBlock (minimum : Nat) (g : Coord) (a : Fin 6) : List (List Int) :=
  ((List.range 64).flatMap fun t => degreeRow minimum g a (degreePattern t)) ++
    (((List.ofFn (fun d : Fin 7 => d)).filter fun d => decide (d.val < minimum)).map fun d =>
      [literal (degreeThresholdNumber g a d) true])

theorem patternCount_eq_freq {D : Design 6} (hD : Linear D) (g : Coord) (a : Fin 6) :
    patternCount (fun b => (encode D).pair (degreeNeighborPair g a b)) =
      freq D (g,a) := by
  have hneq : (g,a).1 ≠ degreePartner g := degreePartner_ne g
  have he : (univ.filter fun b : Fin 6 => (encode D).pair (degreeNeighborPair g a b) = true) =
      neighbors D (g,a) (degreePartner g) := by
    ext b
    rw [mem_filter, mem_neighbors hneq, pair_encode]
    simp only [mem_univ, true_and, degreeNeighborPair]
    split
    · rfl
    · exact ⟨used_symm,used_symm⟩
  unfold patternCount
  rw [he,card_neighbors hD hneq]

/-- Any valuation with the intended pair/threshold values and the branch's
minimum and anchor degree satisfies every archived threshold-block clause. -/
theorem degreeBlock_holds (v : Nat → Bool) (minimum : Nat) (g : Coord) (a : Fin 6)
    (qty : Nat)
    (hQty : patternCount (fun b => v (pairNumber (degreeNeighborPair g a b))) = qty)
    (hDeg : ∀ d : Fin 7, v (degreeThresholdNumber g a d) = decide (d.val ≤ qty))
    (hValid : degreeAllowed minimum g a qty) :
    ∀ C ∈ degreeBlock minimum g a, NumberedHolds v C := by
  intro C hc
  have mismatch (pat : Fin 6 → Bool)
      (hm : ∃ b, v (pairNumber (degreeNeighborPair g a b)) ≠ pat b) :
      NumberedHolds v (degreeBlocking g a pat) := by
    obtain ⟨b,hb⟩ := hm
    have he : v (pairNumber (degreeNeighborPair g a b)) = !(pat b) := by
      have opposed (u w : Bool) (h : u ≠ w) : u = !w := by
        cases u <;> cases w <;> simp_all
      exact opposed _ _ hb
    have hmem : literal (pairNumber (degreeNeighborPair g a b)) (!(pat b)) ∈ degreeBlocking g a pat :=
      List.mem_ofFn.mpr ⟨b,rfl⟩
    exact holds_literal_of_mem hmem (by
      have := (pairNumber_bounds (degreeNeighborPair g a b)).1
      omega) he
  have extend {xs ys : List Int} (hx : NumberedHolds v xs) :
      NumberedHolds v (xs ++ ys) := by
    obtain ⟨l,hl,hn,hv⟩ := hx
    exact ⟨l,List.mem_append.mpr (Or.inl hl),hn,hv⟩
  rcases List.mem_append.mp hc with hrow | hunit
  · obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hrow
    let pat := degreePattern r
    change C ∈ degreeRow minimum g a pat at hr
    by_cases hm : ∃ b, v (pairNumber (degreeNeighborPair g a b)) ≠ pat b
    · have hs := mismatch pat hm
      by_cases hv : degreeAllowed minimum g a (patternCount pat)
      · simp only [degreeRow,hv,ite_true,List.mem_map] at hr
        obtain ⟨d,_,rfl⟩ := hr
        exact extend hs
      · simp only [degreeRow,hv,ite_false,List.mem_singleton] at hr
        rwa [← hr] at hs
    · push Not at hm
      have hp : (fun b => v (pairNumber (degreeNeighborPair g a b))) = pat := funext hm
      have hCount : patternCount pat = qty := hp ▸ hQty
      have hv : degreeAllowed minimum g a (patternCount pat) := hCount.symm ▸ hValid
      simp only [degreeRow,hv,ite_true,List.mem_map] at hr
      obtain ⟨d,_,rfl⟩ := hr
      apply holds_literal_of_mem (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
        (by have := (degreeThresholdNumber_bounds g a d).1; omega)
      rw [hDeg,hCount]
  · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hunit
    have hlt := of_decide_eq_true (List.mem_filter.mp hd).2
    apply holds_literal_of_mem (List.mem_singleton_self _)
      (by have := (degreeThresholdNumber_bounds g a d).1; omega)
    rw [hDeg]
    exact decide_eq_true (by have := hValid.1; omega)

#print axioms patternCount_eq_freq
#print axioms degreeBlock_holds
#print axioms degreeThresholdNumber_injective

end LatinGap.PairEncoding
