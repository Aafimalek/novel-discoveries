import Erdos430Sqrt.Params

/-!
# The two main estimates with the concrete parameters

* `meanSquare_le`: `∫ |F_θ - F_Θ|² ≤ K₁ / (log Y)⁶`.
* `Fr_long_ge`: `F_Θ(v) ≥ bumpMid · ε / (272 (log Y)²)` for `log (Y - 1) ≤ v ≤ log ((1 + ε/8) Y)`.
-/

open MeasureTheory Complex Real Finset

noncomputable section

namespace Erdos430Sqrt

/-- The coefficients and positions of the products `p k`. -/
def cPK (x : ℕ × ℕ) : ℝ := 1 / ((x.1 : ℝ) * x.2)

def ℓPK (x : ℕ × ℕ) : ℝ := Real.log x.1 + Real.log x.2

/-- The constant in the mean-square bound. -/
def K₁ (ε CMV CH Cφ : ℝ) : ℝ :=
  64 * π ^ 2 * (2 + 2 * CMV) + 16 * CH ^ 2 * (256 / ε + 2 * CMV) +
    16 * Cφ ^ 2 * (1024 / ε + 4 * CMV)

section MeanSquare

variable {ε Y : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hY : 16 ≤ Y)
include hε hε1 hY

theorem θs_pos : 0 < θs ε Y := by
  unfold θs; have := sqrtY_ge hε hε1 hY; positivity

theorem Θs_pos : 0 < Θs Y := by
  unfold Θs; have := logY_ge hε hε1 hY; positivity

theorem norm_bumpHat_le_decay {Cφ : ℝ} (hCφ : ∀ ξ, ξ ^ 2 * ‖bumpHat ξ‖ ≤ Cφ) {ξ : ℝ}
    (hξ : ξ ≠ 0) : ‖bumpHat ξ‖ ≤ Cφ / ξ ^ 2 := by
  rw [le_div_iff₀ (by positivity), mul_comm]; exact hCφ ξ

omit hε hε1 hY in
theorem weight_le_four (a b w : ℝ) : ‖bumpHat (a * w) - bumpHat (b * w)‖ ^ 2 ≤ 4 := by
  have h := (norm_sub_le (bumpHat (a * w)) (bumpHat (b * w))).trans
    (add_le_add (norm_bumpHat_le_one _) (norm_bumpHat_le_one _))
  have h0 := norm_nonneg (bumpHat (a * w) - bumpHat (b * w))
  nlinarith

omit hε hε1 hY in
theorem weight_small {a b w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖bumpHat (a * w) - bumpHat (b * w)‖ ^ 2 ≤ (2 * π * (a + b) * |w|) ^ 2 := by
  have h1 := norm_bumpHat_sub_one_le (a * w)
  have h2 := norm_bumpHat_sub_one_le (b * w)
  have h : ‖bumpHat (a * w) - bumpHat (b * w)‖ ≤ 2 * π * (a + b) * |w| := by
    calc ‖bumpHat (a * w) - bumpHat (b * w)‖
        = ‖(bumpHat (a * w) - 1) - (bumpHat (b * w) - 1)‖ := by ring_nf
      _ ≤ ‖bumpHat (a * w) - 1‖ + ‖bumpHat (b * w) - 1‖ := norm_sub_le _ _
      _ ≤ 2 * π * |a * w| + 2 * π * |b * w| := add_le_add h1 h2
      _ = 2 * π * (a + b) * |w| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]; ring
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

omit hε hε1 hY in
theorem weight_decay {a b w Cφ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hw : w ≠ 0)
    (hCφ : ∀ ξ, ξ ^ 2 * ‖bumpHat ξ‖ ≤ Cφ) :
    ‖bumpHat (a * w) - bumpHat (b * w)‖ ^ 2 ≤ 4 * Cφ ^ 2 / (a * w) ^ 4 := by
  have hb : 0 < b := ha.trans_le hab
  have haw : a * w ≠ 0 := mul_ne_zero ha.ne' hw
  have hbw : b * w ≠ 0 := mul_ne_zero hb.ne' hw
  have h1 : ‖bumpHat (a * w)‖ ≤ Cφ / (a * w) ^ 2 := by
    rw [le_div_iff₀ (by positivity), mul_comm]; exact hCφ _
  have h2 : ‖bumpHat (b * w)‖ ≤ Cφ / (a * w) ^ 2 := by
    have hle : (a * w) ^ 2 ≤ (b * w) ^ 2 := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le hab 2) (sq_nonneg w)
    have hCφ0 : 0 ≤ Cφ := (mul_nonneg (sq_nonneg 1) (norm_nonneg _)).trans (hCφ 1)
    calc ‖bumpHat (b * w)‖ ≤ Cφ / (b * w) ^ 2 := by
          rw [le_div_iff₀ (by positivity), mul_comm]; exact hCφ _
      _ ≤ Cφ / (a * w) ^ 2 := div_le_div_of_nonneg_left hCφ0 (by positivity) hle
  have h := (norm_sub_le (bumpHat (a * w)) (bumpHat (b * w))).trans (add_le_add h1 h2)
  have h0 := norm_nonneg (bumpHat (a * w) - bumpHat (b * w))
  calc ‖bumpHat (a * w) - bumpHat (b * w)‖ ^ 2 ≤ (Cφ / (a * w) ^ 2 + Cφ / (a * w) ^ 2) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = 4 * Cφ ^ 2 / (a * w) ^ 4 := by field_simp; ring

/-- **The mean-square bound.** -/
theorem meanSquare_le {CMV CH Cφ : ℝ} (hCMV : 0 ≤ CMV)
    (hMV : ∀ (N : ℕ) (b : ℕ → ℂ) (T : ℝ), 0 ≤ T →
      ∫ t in -T..T, mvSum N b t ≤ (2 * T + CMV * N) * ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2)
    (hPS : ∀ P₁ P₂ : ℝ, √Y / 4 ≤ P₁ → P₂ ≤ 4 * √Y → ∀ t : ℝ, 1 ≤ |t| → |t| ≤ Y ^ 2 →
      ‖∑ p ∈ (Icc ⌈P₁⌉₊ ⌊P₂⌋₊).filter Nat.Prime,
          (p : ℂ)⁻¹ * Complex.exp (-(((t * Real.log p : ℝ) : ℂ) * I))‖ ≤
        CH * (1 / (|t| * Real.log Y) + 1 / Real.log Y ^ 5))
    (hCφ : ∀ ξ, ξ ^ 2 * ‖bumpHat ξ‖ ≤ Cφ)
    (hθΘ : θs ε Y ≤ Θs Y) (hZ : 2 * π * (Real.log Y ^ 2 / θs ε Y) ≤ Y ^ 2)
    (hT : 6 * Real.log Y ^ 3 ≤ √Y) :
    ∫ v, ‖D (primesP ε Y ×ˢ primesK Y) cPK ℓPK (θs ε Y) (Θs Y) v‖ ^ 2 ≤
      K₁ ε CMV CH Cφ / Real.log Y ^ 6 := by
  set L := Real.log Y with hL
  set θ := θs ε Y with hθdef
  set Θ := Θs Y with hΘdef
  have hL1 : 1 ≤ L := logY_ge hε hε1 hY
  have hs4 : 4 ≤ √Y := sqrtY_ge hε hε1 hY
  have hθ : 0 < θ := θs_pos hε hε1 hY
  have hΘ : 0 < Θ := Θs_pos hε hε1 hY
  have hCφ0 : 0 ≤ Cφ := (mul_nonneg (sq_nonneg 1) (norm_nonneg _)).trans (hCφ 1)
  rw [integral_norm_sq_D _ _ _ hθ hΘ]
  have hfun : (fun w => ‖dirichlet (primesP ε Y ×ˢ primesK Y) cPK ℓPK w‖ ^ 2 *
      ‖bumpHat (θ * w) - bumpHat (Θ * w)‖ ^ 2) = fun w =>
        ‖polyW (primesP ε Y) w‖ ^ 2 * ‖polyW (primesK Y) w‖ ^ 2 *
          ‖bumpHat (θ * w) - bumpHat (Θ * w)‖ ^ 2 := by
    funext w
    rw [show cPK = fun x : ℕ × ℕ => 1 / ((x.1 : ℝ) * x.2) from rfl,
      show ℓPK = fun x : ℕ × ℕ => Real.log x.1 + Real.log x.2 from rfl,
      dirichlet_prod, norm_mul, mul_pow]
  have hint := integrable_fourier_side (primesP ε Y ×ˢ primesK Y) cPK ℓPK hθ hΘ
  rw [hfun] at hint ⊢
  -- the hypotheses of `integral_le_of_bounds`
  have hσP : ∀ w, ‖polyW (primesP ε Y) w‖ ≤ 2 := fun w =>
    (norm_polyW_le _ w).trans (sum_inv_primesP_le hε hε1 hY)
  have hθL : θ ≤ 1 / L := by
    refine hθΘ.trans ?_
    rw [hΘdef, Θs, ← hL]
    apply one_div_le_one_div_of_le (by positivity)
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
  have hT₀Z : L ^ 3 ≤ L ^ 2 / θ := by
    rw [le_div_iff₀ hθ]
    calc L ^ 3 * θ ≤ L ^ 3 * (1 / L) := mul_le_mul_of_nonneg_left hθL (by positivity)
      _ = L ^ 2 := by field_simp
  have hM : ∀ w, L ^ 3 ≤ |w| → |w| ≤ L ^ 2 / θ →
      ‖polyW (primesP ε Y) w‖ ≤ 2 * |CH| / L ^ 4 := by
    intro w hw1 hw2
    rw [polyW_primesP_eq hε hε1 hY]
    have ht1 : 1 ≤ |2 * π * w| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have : 1 ≤ |w| := (one_le_pow₀ hL1).trans hw1
      nlinarith [Real.pi_gt_three]
    have ht2 : |2 * π * w| ≤ Y ^ 2 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      exact (mul_le_mul_of_nonneg_left hw2 (by positivity)).trans hZ
    have hP1 : √Y / 4 ≤ P₁ ε Y := by
      have := P₁_ge hε hε1 hY; linarith
    have hP2 : P₂ ε Y ≤ 4 * √Y := by
      have := P₂_le hε hε1 hY; linarith
    refine (hPS _ _ hP1 hP2 _ ht1 ht2).trans ?_
    have htw : L ^ 3 ≤ |2 * π * w| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      nlinarith [Real.pi_gt_three, abs_nonneg w]
    have hinv1 : 1 / (|2 * π * w| * L) ≤ 1 / L ^ 4 := by
      apply one_div_le_one_div_of_le (by positivity)
      calc L ^ 4 = L ^ 3 * L := by ring
        _ ≤ |2 * π * w| * L := mul_le_mul_of_nonneg_right htw (by positivity)
    have hinv2 : 1 / L ^ 5 ≤ 1 / L ^ 4 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hL1 (by norm_num))
    calc CH * (1 / (|2 * π * w| * L) + 1 / L ^ 5) ≤ |CH| * (1 / (|2 * π * w| * L) + 1 / L ^ 5) :=
          mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity)
      _ ≤ |CH| * (1 / L ^ 4 + 1 / L ^ 4) :=
          mul_le_mul_of_nonneg_left (add_le_add hinv1 hinv2) (abs_nonneg _)
      _ = 2 * |CH| / L ^ 4 := by ring
  have hMVT : ∀ R, 0 ≤ R → ∫ w in -R..R, ‖polyW (primesK Y) w‖ ^ 2 ≤ 8 / √Y * R + 2 * CMV :=
    fun R hR => mvt_primesK hε hε1 hY hCMV hMV hR
  have hbound := integral_le_of_bounds (polyW (primesP ε Y)) (polyW (primesK Y))
    (fun w => ‖bumpHat (θ * w) - bumpHat (Θ * w)‖ ^ 2) hint (polyW_continuous _)
    (fun w => by positivity) hσP (by positivity) hT₀Z hM (by positivity)
    (by positivity) hMVT (fun w hw => (weight_small hθ.le hΘ.le).trans
      (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left hw (by positivity)) 2))
    (fun w => weight_le_four θ Θ w) hθ (by positivity)
    (fun w hw => weight_decay hθ hθΘ hw hCφ)
  refine hbound.trans ?_
  -- the arithmetic
  have hs : 0 < √Y := by linarith
  have hθval : θ = ε / (32 * √Y) := rfl
  have hΘval : Θ = 1 / L ^ 6 := rfl
  have hθZ : θ * (L ^ 2 / θ) = L ^ 2 := by field_simp
  have hAZ : 8 / √Y * (L ^ 2 / θ) = 256 * L ^ 2 / ε := by rw [hθval]; field_simp; ring
  have hW₀ : (2 * π * (θ + Θ) * L ^ 3) ^ 2 ≤ 16 * π ^ 2 / L ^ 6 := by
    have h1 : 2 * π * (θ + Θ) * L ^ 3 ≤ 4 * π / L ^ 3 := by
      have : (θ + Θ) * L ^ 3 ≤ 2 / L ^ 3 := by
        rw [hΘval]
        have h2 : θ * L ^ 3 ≤ 1 / L ^ 3 := by
          calc θ * L ^ 3 ≤ (1 / L ^ 6) * L ^ 3 := mul_le_mul_of_nonneg_right
                (hθΘ.trans_eq hΘval) (by positivity)
            _ = 1 / L ^ 3 := by field_simp
        have h3 : (1 / L ^ 6) * L ^ 3 = 1 / L ^ 3 := by field_simp
        rw [add_mul, show (2 : ℝ) / L ^ 3 = 1 / L ^ 3 + 1 / L ^ 3 by ring]; linarith
      calc 2 * π * (θ + Θ) * L ^ 3 = 2 * π * ((θ + Θ) * L ^ 3) := by ring
        _ ≤ 2 * π * (2 / L ^ 3) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = 4 * π / L ^ 3 := by ring
    calc (2 * π * (θ + Θ) * L ^ 3) ^ 2 ≤ (4 * π / L ^ 3) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = 16 * π ^ 2 / L ^ 6 := by field_simp; ring
  have hAT : 8 / √Y * L ^ 3 ≤ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hs]; linarith
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hL6 : 0 < L ^ 6 := by positivity
  -- term 1
  have t1 : 2 ^ 2 * (2 * π * (θ + Θ) * L ^ 3) ^ 2 * (8 / √Y * L ^ 3 + 2 * CMV) ≤
      64 * π ^ 2 * (2 + 2 * CMV) / L ^ 6 := by
    calc 2 ^ 2 * (2 * π * (θ + Θ) * L ^ 3) ^ 2 * (8 / √Y * L ^ 3 + 2 * CMV)
        ≤ 2 ^ 2 * (16 * π ^ 2 / L ^ 6) * (2 + 2 * CMV) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hW₀ (by norm_num)) (by linarith)
            (by positivity) (by positivity)
      _ = 64 * π ^ 2 * (2 + 2 * CMV) / L ^ 6 := by ring
  -- term 2
  have t2 : 4 * (2 * |CH| / L ^ 4) ^ 2 * (8 / √Y * (L ^ 2 / θ) + 2 * CMV) ≤
      16 * CH ^ 2 * (256 / ε + 2 * CMV) / L ^ 6 := by
    rw [hAZ]
    have hle : 256 * L ^ 2 / ε + 2 * CMV ≤ (256 / ε + 2 * CMV) * L ^ 2 := by
      rw [show 256 * L ^ 2 / ε = 256 / ε * L ^ 2 by ring]
      nlinarith
    calc 4 * (2 * |CH| / L ^ 4) ^ 2 * (256 * L ^ 2 / ε + 2 * CMV)
        ≤ 4 * (2 * |CH| / L ^ 4) ^ 2 * ((256 / ε + 2 * CMV) * L ^ 2) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 16 * CH ^ 2 * (256 / ε + 2 * CMV) / L ^ 6 := by
          rw [div_pow, mul_pow, sq_abs]; field_simp; ring
  -- term 3
  have t3 : 2 ^ 2 * (4 * Cφ ^ 2) / (θ * (L ^ 2 / θ)) ^ 4 *
      (4 * (8 / √Y) * (L ^ 2 / θ) + 2 * (2 * CMV)) ≤
      16 * Cφ ^ 2 * (1024 / ε + 4 * CMV) / L ^ 6 := by
    rw [hθZ, mul_assoc 4, hAZ]
    have hle : 4 * (256 * L ^ 2 / ε) + 2 * (2 * CMV) ≤ (1024 / ε + 4 * CMV) * L ^ 2 := by
      rw [show 4 * (256 * L ^ 2 / ε) = 1024 / ε * L ^ 2 by ring]
      nlinarith
    calc 2 ^ 2 * (4 * Cφ ^ 2) / (L ^ 2) ^ 4 * (4 * (256 * L ^ 2 / ε) + 2 * (2 * CMV))
        ≤ 2 ^ 2 * (4 * Cφ ^ 2) / (L ^ 2) ^ 4 * ((1024 / ε + 4 * CMV) * L ^ 2) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 16 * Cφ ^ 2 * (1024 / ε + 4 * CMV) / L ^ 6 := by field_simp; ring
  unfold K₁
  rw [add_div, add_div]
  linarith [t1, t2, t3]

end MeanSquare

end Erdos430Sqrt
