import NineSeparatedSubsetSums.GapBlock
import NineSeparatedSubsetSums.FractionReflect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace NineSeparatedSubsetSums

theorem floorCriticalCompl (M x δ : ℝ) (hM : M = 148 + δ)
    (hδ : 0 ≤ δ ∧ δ < 1) (hx : Int.fract x ≤ δ) :
    ⌊M - x⌋ = 148 - ⌊x⌋ := by
  have hxn := Int.fract_nonneg x
  change 0 ≤ x - (⌊x⌋ : ℝ) at hxn
  change x - (⌊x⌋ : ℝ) ≤ δ at hx
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> linarith [hδ.1, hδ.2]

/-- A forward step with the correct rounded increment preserves the rank offset. -/
theorem rankOffset_of_rounded_step (v : ℕ → ℝ) (a : ℕ → ℤ)
    (bound L R i j : ℕ)
    (hgap : ∀ k : ℕ, k + 1 < bound → 1 ≤ v (k + 1) - v k)
    (hL : L ≤ i) (hij : i ≤ j) (hR : j ≤ R) (hb : R < bound)
    (hexcess : v R - v L - ((R - L : ℕ) : ℝ) < 1)
    (hstep : ⌊v j - v i⌋ = a j - a i) :
    (j : ℤ) - a j = (i : ℤ) - a i := by
  rw [rank_difference_is_floor v bound L R i j hgap hL hij hR hb hexcess] at hstep
  omega

/-- The numerical margin in the 149 proof contains both translated real sums. -/
theorem centered_inside_real (v round lo hi T : ℝ)
    (hlo : lo = T / 2 - 197 / 2) (hhi : hi = T / 2 + 197 / 2)
    (hr : T / 2 - 74 ≤ round ∧ round ≤ T / 2 + 74)
    (hv : 0 ≤ v - round ∧ v - round < 9)
    (a b : ℝ) (ha : 0 ≤ a - lo ∧ a - lo < 9)
    (hb : 0 ≤ b - hi ∧ b - hi < 9) :
    a < v ∧ v < b := by
  constructor <;> linarith [hr.1, hr.2, hv.1, hv.2, ha.2, hb.1]

#print axioms floorCriticalCompl
#print axioms rankOffset_of_rounded_step
#print axioms centered_inside_real

end NineSeparatedSubsetSums
