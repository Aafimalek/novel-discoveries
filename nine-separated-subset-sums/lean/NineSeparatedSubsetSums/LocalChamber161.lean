import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace NineSeparatedSubsetSums

/-- A local certificate: these nine consecutively ordered subset-sum gaps
of the classical 161 construction already force its last weight to be
at least 161. Other order chambers are not excluded by this result. -/
theorem chamber161_local (w : Fin 9 → ℝ)
    (h0 : (1 : ℝ) ≤ w 7 - w 6)
    (h1 : (1 : ℝ) ≤ w 8 - w 7)
    (h2 : (1 : ℝ) ≤ (w 5 + w 6) - (w 4 + w 8))
    (h3 : (1 : ℝ) ≤ (w 2 + w 3 + w 4) - (w 1 + w 7 + w 8))
    (h4 : (1 : ℝ) ≤ (w 3 + w 4 + w 5) - (w 2 + w 7 + w 8))
    (h5 : (1 : ℝ) ≤ (w 4 + w 5 + w 6) - (w 3 + w 7 + w 8))
    (h6 : (1 : ℝ) ≤ (w 0 + w 1 + w 2 + w 3) - (w 5 + w 7 + w 8))
    (h7 : (1 : ℝ) ≤ (w 1 + w 2 + w 3 + w 4) - (w 0 + w 5 + w 7 + w 8))
    (h8 : (1 : ℝ) ≤ (w 1 + w 6 + w 7 + w 8) - (w 2 + w 3 + w 4 + w 5)) :
    161 ≤ w 8 := by
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8]

#print axioms chamber161_local

end NineSeparatedSubsetSums
