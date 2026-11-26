import Erdos430Sqrt.Fourier
import Erdos430Sqrt.Hypotheses

/-!
# Dirichlet polynomials over sets of integers

`polyW S w = ∑_{n ∈ S} n⁻¹ e(-w log n)` is the Dirichlet polynomial `∑ n^{-1-it}` at
`t = 2π w`, the frequency scale of mathlib's Fourier transform. This file proves its
trivial bound, transfers the mean value hypothesis to this scale, and factors the
polynomial of products `p k` as the product of the two polynomials.
-/

open MeasureTheory Complex Real Finset

noncomputable section

namespace Erdos430Sqrt

/-- `∑_{n ∈ S} n⁻¹ e(-w log n)`. -/
def polyW (S : Finset ℕ) (w : ℝ) : ℂ :=
  ∑ n ∈ S, (n : ℂ)⁻¹ * Complex.exp (((-2 * π * Real.log n * w : ℝ) : ℂ) * I)

theorem polyW_continuous (S : Finset ℕ) : Continuous (polyW S) := by
  unfold polyW
  refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
  exact Complex.continuous_exp.comp
    ((continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)

theorem norm_exp_real_mul_I (r : ℝ) : ‖Complex.exp ((r : ℂ) * I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I r

/-- Trivial bound: `‖polyW S w‖ ≤ ∑_{n ∈ S} 1/n`. -/
theorem norm_polyW_le (S : Finset ℕ) (w : ℝ) : ‖polyW S w‖ ≤ ∑ n ∈ S, (1 / (n : ℝ)) := by
  unfold polyW
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_exp_real_mul_I, mul_one, norm_inv, Complex.norm_natCast, one_div]

/-- If every element of `S` is at least `a > 0`, then `∑_{n ∈ S} 1/n ≤ #S / a`. -/
theorem sum_inv_le_card_div {S : Finset ℕ} {a : ℝ} (ha : 0 < a) (hS : ∀ n ∈ S, a ≤ n) :
    ∑ n ∈ S, (1 / (n : ℝ)) ≤ S.card / a := by
  calc ∑ n ∈ S, (1 / (n : ℝ)) ≤ ∑ _n ∈ S, 1 / a :=
        sum_le_sum fun n hn => one_div_le_one_div_of_le ha (hS n hn)
    _ = S.card / a := by rw [sum_const, nsmul_eq_mul, mul_one_div]

theorem sum_inv_sq_le_card_div {S : Finset ℕ} {a : ℝ} (ha : 0 < a) (hS : ∀ n ∈ S, a ≤ n) :
    ∑ n ∈ S, (1 / (n : ℝ)) ^ 2 ≤ S.card / a ^ 2 := by
  calc ∑ n ∈ S, (1 / (n : ℝ)) ^ 2 ≤ ∑ _n ∈ S, (1 / a) ^ 2 := by
        refine sum_le_sum fun n hn => ?_
        exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le ha (hS n hn)) 2
    _ = S.card / a ^ 2 := by rw [sum_const, nsmul_eq_mul, one_div_pow, mul_one_div]

/-- The integrand of the mean value hypothesis. -/
def mvSum (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℝ :=
  ‖∑ n ∈ Icc 1 N, b n * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I))‖ ^ 2

/-- The coefficients `1/n` on `S` and `0` elsewhere. -/
def coeffOn (S : Finset ℕ) (n : ℕ) : ℂ := if n ∈ S then (n : ℂ)⁻¹ else 0

theorem mvSum_coeffOn {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 1 N) (w : ℝ) :
    mvSum N (coeffOn S) (2 * π * w) = ‖polyW S w‖ ^ 2 := by
  unfold mvSum polyW
  congr 2
  rw [← Finset.sum_subset hS (fun n _ hn => by simp [coeffOn, hn])]
  refine sum_congr rfl fun n hn => ?_
  rw [coeffOn, if_pos hn]
  congr 2
  push_cast
  ring

theorem sum_norm_coeffOn {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 1 N) :
    ∑ n ∈ Icc 1 N, ‖coeffOn S n‖ ^ 2 = ∑ n ∈ S, (1 / (n : ℝ)) ^ 2 := by
  rw [← Finset.sum_subset hS (fun n _ hn => by simp [coeffOn, hn])]
  refine sum_congr rfl fun n hn => ?_
  rw [coeffOn, if_pos hn, norm_inv, Complex.norm_natCast, one_div]

/-- The mean value hypothesis at the frequency scale `t = 2π w`. -/
theorem mvt_polyW {C : ℝ}
    (hMV : ∀ (N : ℕ) (b : ℕ → ℂ) (T : ℝ), 0 ≤ T →
      ∫ t in -T..T, mvSum N b t ≤ (2 * T + C * N) * ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2)
    {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 1 N) {R : ℝ} (hR : 0 ≤ R) :
    ∫ w in -R..R, ‖polyW S w‖ ^ 2 ≤ (2 * R + C * N / (2 * π)) * ∑ n ∈ S, (1 / (n : ℝ)) ^ 2 := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hfun : (fun w => ‖polyW S w‖ ^ 2) = fun w => mvSum N (coeffOn S) (2 * π * w) :=
    funext fun w => (mvSum_coeffOn hS w).symm
  have hsub : ∫ w in -R..R, ‖polyW S w‖ ^ 2 =
      (2 * π)⁻¹ * ∫ t in (2 * π) * (-R)..(2 * π) * R, mvSum N (coeffOn S) t := by
    rw [hfun, intervalIntegral.integral_comp_mul_left (fun t => mvSum N (coeffOn S) t) h2π,
      smul_eq_mul]
  have hMV' := hMV N (coeffOn S) (2 * π * R) (by positivity)
  rw [sum_norm_coeffOn hS, show -(2 * π * R) = 2 * π * (-R) by ring] at hMV'
  rw [hsub]
  calc (2 * π)⁻¹ * ∫ t in (2 * π) * (-R)..(2 * π) * R, mvSum N (coeffOn S) t
      ≤ (2 * π)⁻¹ * ((2 * (2 * π * R) + C * N) * ∑ n ∈ S, (1 / (n : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hMV' (by positivity)
    _ = (2 * R + C * N / (2 * π)) * ∑ n ∈ S, (1 / (n : ℝ)) ^ 2 := by
        field_simp

/-- The Dirichlet polynomial of products `p k` factors. -/
theorem dirichlet_prod (Ps Ks : Finset ℕ) (w : ℝ) :
    dirichlet (Ps ×ˢ Ks) (fun x => 1 / ((x.1 : ℝ) * x.2))
        (fun x => Real.log x.1 + Real.log x.2) w = polyW Ps w * polyW Ks w := by
  unfold dirichlet polyW
  rw [sum_product, sum_mul_sum]
  refine sum_congr rfl fun p _ => sum_congr rfl fun k _ => ?_
  have hexp : Complex.exp (((-2 * π * (Real.log p + Real.log k) * w : ℝ) : ℂ) * I) =
      Complex.exp (((-2 * π * Real.log p * w : ℝ) : ℂ) * I) *
        Complex.exp (((-2 * π * Real.log k * w : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hexp]
  push_cast
  ring

end Erdos430Sqrt
