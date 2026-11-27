import OrbitArithmetic

namespace G449OrbitArithmetic

structure Vertex where
  coeffs : List Int
  colour : Nat

structure Edge where
  a : Nat
  b : Nat
  d : Nat
  flip : Bool

def Edge.validBool (vertices : Nat → Vertex) (dirs : Nat → V) (e : Edge) : Bool :=
  let a := vertices e.a
  let b := vertices e.b
  decide (e.a < 449) && decide (e.b < 449) && decide (e.d < 49) &&
    decide (a.colour ≠ b.colour) &&
    (List.range 12).all (fun i =>
      a.coeffs.getD i 0 - b.coeffs.getD i 0 ==
        if e.flip then -dirs e.d i else dirs e.d i)

theorem Edge.validBool_sound (vertices : Nat → Vertex) (dirs : Nat → V) (e : Edge)
    (h : e.validBool vertices dirs = true) :
    e.a < 449 ∧ e.b < 449 ∧ e.d < 49 ∧ (vertices e.a).colour ≠ (vertices e.b).colour ∧
    ∀ i < 12, (vertices e.a).coeffs.getD i 0 - (vertices e.b).coeffs.getD i 0 =
      if e.flip then -dirs e.d i else dirs e.d i := by
  unfold Edge.validBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1,h.1.1.1.2,h.1.1.2,h.1.2,fun i hi => h.2 i (List.mem_range.mpr hi)⟩

#print axioms Edge.validBool_sound

end G449OrbitArithmetic
