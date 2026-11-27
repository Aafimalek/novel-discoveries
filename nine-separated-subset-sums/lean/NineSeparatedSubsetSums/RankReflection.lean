import Mathlib.Order.Fin.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace NineSeparatedSubsetSums

/-- Under increasing scores, reflection of all scores around the midpoint
reverses the finite ranks. This applies to taking subset complements. -/
theorem rank_reflect_of_score {X : Type*} {n : ℕ}
    (r : X ≃ Fin n) (v : Fin n → ℝ) (hv : StrictMono v)
    (f : X → X) (T : ℝ)
    (hf : ∀ x, v (r (f x)) = T - v (r x)) (x : X) :
    r (f x) = Fin.rev (r x) := by
  let g (j : Fin n) := r (f (r.symm j))
  have e (j : Fin n) : v (g j) = T - v j := by simpa [g] using hf (r.symm j)
  have anti : StrictAnti g := by
    intro i j hij
    apply hv.lt_iff_lt.mp
    rw [e i, e j]
    have hj := hv hij
    linarith
  have mid : g ∘ Fin.rev = id := (anti.comp Fin.rev_strictAnti).eq_id
  have h := congrFun mid (Fin.rev (r x))
  simpa [Function.comp_def, g] using h

#print axioms rank_reflect_of_score

end NineSeparatedSubsetSums
