import Init

namespace G449OrbitArithmetic

abbrev V := Nat → Int

/-- Integer coefficient rotation by the sixth power of the primitive root. -/
def spin (v : V) (i : Nat) : Int :=
  match i with
  | 0 => -v 6 + v 7 - v 8
  | 1 => -v 6 - v 9
  | 2 => -v 7 - v 10
  | 3 => v 6 - v 7 - v 11
  | 4 => v 6
  | 5 => v 7
  | 6 => v 0 - v 6 + v 7
  | 7 => v 1 - v 7 + v 8
  | 8 => v 2 + v 6 - v 7 + v 9
  | 9 => v 3 + v 6 + v 10
  | 10 => v 4 + v 7 + v 11
  | 11 => v 5 - v 6 + v 7
  | _ => 0

structure Step where
  prev : Nat
  rank : Nat
  spinNeg : Bool

/-- A branch of the spanning orbit forest is completely arithmetic. -/
def orbitStepBool (dirs : Nat → V) (steps : Nat → Step) (roots : List Nat) (k : Nat) : Bool :=
  if roots.contains k then true else
    let s := steps k
    decide (s.prev < 49) && decide ((steps s.prev).rank < s.rank) &&
    (List.range 12).all (fun i =>
      dirs k i == if s.spinNeg then -spin (dirs s.prev) i else spin (dirs s.prev) i)

theorem orbitStepBool_sound (dirs : Nat → V) (steps : Nat → Step) (roots : List Nat)
    (k : Nat) (h : orbitStepBool dirs steps roots k = true) :
    roots.contains k = true ∨ ((steps k).prev < 49 ∧
      (steps (steps k).prev).rank < (steps k).rank ∧
      ∀ i < 12, dirs k i =
        if (steps k).spinNeg then -spin (dirs (steps k).prev) i
        else spin (dirs (steps k).prev) i) := by
  cases H : roots.contains k with
  | true => exact Or.inl rfl
  | false =>
    unfold orbitStepBool at h
    simp only [H, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    exact Or.inr ⟨h.1.1, h.1.2, fun i hi => h.2 i (List.mem_range.mpr hi)⟩

def phiLow : List Int := [1,1,0,-1,-1,0,1,0,-1,-1,0,1]

def shift (v : V) (i : Nat) : Int :=
  (if 0 < i then v (i-1) else 0) - v 11 * phiLow.getD i 0

def testPowers (pow : Nat → V) : Bool :=
  ((List.range 12).all (fun i => pow 0 i == if i = 0 then 1 else 0)) &&
    (List.range 53).all (fun k => (List.range 12).all (fun i => pow (k+1) i == shift (pow k) i))

def normBare (pow : Nat → V) (v : V) (r : Nat) : Int :=
  (List.ofFn (fun i : Fin 12 =>
    (List.ofFn (fun j : Fin 12 => v i.val * v j.val * pow (i.val+(42-j.val)) r)).sum)).sum

def testNorm (pow : Nat → V) (v : V) : Bool :=
  (List.range 12).all (fun i => normBare pow v i == if i = 0 then 2401 else 0)

theorem testNorm_sound (pow : Nat → V) (v : V) (h : testNorm pow v = true)
    (i : Nat) (hi : i < 12) : normBare pow v i = if i = 0 then 2401 else 0 :=
  beq_iff_eq.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi))

#print axioms orbitStepBool_sound
#print axioms testNorm_sound

end G449OrbitArithmetic
