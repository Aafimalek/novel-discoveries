import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Basic

namespace NineSeparatedSubsetSums

private theorem deficitCost99 (U x : ℤ) (hu : 91 ≤ U) (h0 : 0 ≤ x) (hUx : x ≤ U) :
    132 * min 50 (U-x) ≤ U^2 - x^2 := by
  by_cases h : 50 ≤ U-x
  · rw [min_eq_left h]
    have h₁ : 0 ≤ U-50-x := by omega
    have h₂ : 0 ≤ U-50+x := by omega
    nlinarith only [mul_nonneg h₁ h₂, hu]
  · rw [min_eq_right (by omega : U-x ≤ 50)]
    have h₁ : 0 ≤ U-x := by omega
    have h₂ : 0 ≤ U+x-132 := by omega
    nlinarith only [mul_nonneg h₁ h₂]

private theorem minQuadSum99 (x₁ x₂ x₃ x₄ : ℤ)
    (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂) (h₃ : 0 ≤ x₃) (h₄ : 0 ≤ x₄)
    (ht : 50 ≤ x₁ + x₂ + x₃ + x₄) :
    50 ≤ min 50 x₁ + min 50 x₂ + min 50 x₃ + min 50 x₄ := by
  by_cases b₁ : 50 ≤ x₁ <;> by_cases b₂ : 50 ≤ x₂ <;>
    by_cases b₃ : 50 ≤ x₃ <;> by_cases b₄ : 50 ≤ x₄ <;> omega

/-- Sharp second-moment cap from a 69-wide four-choice shelf among
the eight smaller weights, when those weights are at most 99. -/
theorem secondLe99MomentUpper (a b c d e f g h : ℤ)
    (apos : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e) (hef : e < f) (hfg : f < g) (hgh : g < h) (hhi : h ≤ 99)
    (noPair : e+h ≠ f+g)
    (span : 69 ≤ (e+f+g+h) - (a+b+c+d)) :
    a^2+b^2+c^2+d^2+e^2+f^2+g^2+h^2+148^2 ≤ 87373 := by
  have eU : e ≤ 95 := by omega
  have aU : a ≤ 91 := by omega
  have bU : b ≤ 92 := by omega
  have cU : c ≤ 93 := by omega
  have dU : d ≤ 94 := by omega
  have fU : f ≤ 97 := by omega
  have gU : g ≤ 98 := by omega
  have k₁ := deficitCost99 91 a (by decide) apos aU
  have k₂ := deficitCost99 92 b (by decide) (by omega) bU
  have k₃ := deficitCost99 93 c (by decide) (by omega) cU
  have k₄ := deficitCost99 94 d (by decide) (by omega) dU
  have k₅ := minQuadSum99 (91-a) (92-b) (93-c) (94-d)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have i₁ := mul_nonneg (show 0 ≤ 95-e by omega) (show 0 ≤ 95+e by omega)
  have i₂ := mul_nonneg (show 0 ≤ 97-f by omega) (show 0 ≤ 97+f by omega)
  have i₃ := mul_nonneg (show 0 ≤ 98-g by omega) (show 0 ≤ 98+g by omega)
  have i₄ := mul_nonneg (show 0 ≤ 99-h by omega) (show 0 ≤ 99+h by omega)
  nlinarith only [k₁,k₂,k₃,k₄,k₅,i₁,i₂,i₃,i₄]

#print axioms secondLe99MomentUpper

end NineSeparatedSubsetSums
