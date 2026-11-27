import NineSeparatedSubsetSums.GapBlock
import NineSeparatedSubsetSums.FractionReflect
import Mathlib.Tactic.Linarith

namespace NineSeparatedSubsetSums

/-- Any forward score difference in the critical interval has fractional
part at most the excess over unit gaps. -/
theorem critical_difference_fract (v : ℕ → ℝ) (bound L R i j : ℕ)
    (hgap : ∀ k : ℕ, k + 1 < bound → 1 ≤ v (k + 1) - v k)
    (hL : L ≤ i) (hij : i ≤ j) (hR : j ≤ R) (hb : R < bound)
    (hexcess : v R - v L - ((R - L : ℕ) : ℝ) < 1) :
    Int.fract (v j - v i) ≤ v R - v L - ((R - L : ℕ) : ℝ) := by
  change v j - v i - (⌊v j - v i⌋ : ℝ) ≤ _
  rw [rank_difference_is_floor v bound L R i j hgap hL hij hR hb hexcess, Int.cast_natCast]
  have h := (subinterval_rank_bounds v bound L R i j hgap hL hij hR hb).2
  linarith

/-- A lifted direction edge inside the critical interval detects the original
coordinate's fractional part in either orientation. -/
theorem coordinate_fract_of_lift (v : ℕ → ℝ) (bound L R i j : ℕ) (x M δ : ℝ)
    (hgap : ∀ k : ℕ, k + 1 < bound → 1 ≤ v (k + 1) - v k)
    (hL : L ≤ i) (hij : i ≤ j) (hR : j ≤ R) (hb : R < bound)
    (hδ : 0 ≤ δ ∧ δ < 1)
    (hexcess : v R - v L - ((R - L : ℕ) : ℝ) = δ)
    (hM : M = 148 + δ)
    (hstep : v j - v i = x ∨ v j - v i = M - x) :
    Int.fract x ≤ δ := by
  have he : v R - v L - ((R - L : ℕ) : ℝ) < 1 := hexcess ▸ hδ.2
  have h := critical_difference_fract v bound L R i j hgap hL hij hR hb he
  rw [hexcess] at h
  rcases hstep with hstep | hstep
  · rwa [hstep] at h
  · rw [hstep, hM] at h
    exact fract_le_of_reflected_fract_le 148 δ x hδ.1 (by simpa using h)

#print axioms critical_difference_fract
#print axioms coordinate_fract_of_lift

end NineSeparatedSubsetSums
