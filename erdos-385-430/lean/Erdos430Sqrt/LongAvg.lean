import Erdos430Sqrt.Bounds

/-!
# The long-average lower bound with the concrete parameters

For `log (Y - 1) ≤ v ≤ log ((1 + ε/8) Y)`, `F_Θ(v) ≥ bumpMid · ε / (272 (log Y)²)`.
-/

open MeasureTheory Complex Real Finset

noncomputable section

namespace Erdos430Sqrt

theorem one_sub_exp_neg_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x / 2 ≤ 1 - Real.exp (-x) := by
  have h1 : Real.exp (-x) * (1 + x) ≤ 1 := by
    have := Real.add_one_le_exp x
    calc Real.exp (-x) * (1 + x) ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-x)]

theorem log_three_quarters_ge : -(1 / 3 : ℝ) ≤ Real.log (3 / 4) := by
  have h4 : Real.log (4 / 3) ≤ 4 / 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h5 : Real.log (3 / 4) = -Real.log (4 / 3) := by
    rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
  linarith

section LongAvg

variable {ε Y : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hY : 16 ≤ Y)
include hε hε1 hY

theorem logY_ge_two : 2 ≤ Real.log Y := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h0 := Real.exp_pos 1
  nlinarith

theorem log_sqrt_eq : Real.log √Y = Real.log Y / 2 := Real.log_sqrt (by linarith)

theorem P₂_sub_P₁_ge : ε / 17 * P₂ ε Y ≤ P₂ ε Y - P₁ ε Y := by
  have h := P₁_mul_le_P₂ hε hε1 hY
  have hP₁0 : 0 ≤ P₁ ε Y := by linarith [P₁_ge hε hε1 hY, sqrtY_ge hε hε1 hY]
  have hc : 1 ≤ (1 - ε / 17) * (1 + ε / 16) := by
    have heq : (1 - ε / 17) * (1 + ε / 16) = 1 + ε * (1 - ε) / 272 := by ring
    rw [heq]
    have := mul_nonneg hε.le (sub_nonneg.mpr hε1)
    linarith
  have h2 : (1 - ε / 17) * (P₁ ε Y * (1 + ε / 16)) ≤ (1 - ε / 17) * P₂ ε Y :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have h3 := mul_le_mul_of_nonneg_left hc hP₁0
  nlinarith

theorem log_P₁_ge : Real.log Y / 4 ≤ Real.log (P₁ ε Y) := by
  have hs4 := sqrtY_ge hε hε1 hY
  have h1 : Real.log (3 / 4 * √Y) ≤ Real.log (P₁ ε Y) :=
    Real.log_le_log (by positivity) (P₁_ge hε hε1 hY)
  have h2 : Real.log (3 / 4 * √Y) = Real.log (3 / 4) + Real.log Y / 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), log_sqrt_eq hε hε1 hY]
  have h3 := log_three_quarters_ge
  have h4 := logY_ge_two hε hε1 hY
  linarith

/-- `∑_{p} 1/p ≥ ε / (34 log Y)`. -/
theorem sum_inv_primesP_ge {Cθ : ℝ} (hCθ : 0 ≤ Cθ)
    (hθH : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ Cθ * x / Real.log x ^ 10)
    (hθout : 2 * 4 ^ 10 * Cθ / Real.log Y ^ 10 ≤ ε / 34) :
    ε / (34 * Real.log Y) ≤ ∑ p ∈ primesP ε Y, (1 / (p : ℝ)) := by
  have hs4 := sqrtY_ge hε hε1 hY
  have hP₁ := P₁_ge hε hε1 hY
  have hP₂ := P₂_le hε hε1 hY
  have hP₁₂ := P₁_le_P₂ hε hε1 hY
  have hL2 := logY_ge_two hε hε1 hY
  have hP₁2 : 2 ≤ P₁ ε Y := by linarith
  have hP₂pos : 0 < P₂ ε Y := by linarith
  have hlogP₂ : 0 < Real.log (P₂ ε Y) := Real.log_pos (by linarith)
  have hsubP : (Ioc ⌊P₁ ε Y⌋₊ ⌊P₂ ε Y⌋₊).filter Nat.Prime ⊆ primesP ε Y := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    simp only [primesP, mem_filter, mem_Icc]
    refine ⟨⟨?_, hp.1.2⟩, hp.2⟩
    have := Nat.lt_floor_add_one (P₁ ε Y)
    have h2 : ((⌊P₁ ε Y⌋₊ : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hp.1.1
    exact Nat.ceil_le.mpr (by linarith)
  have hlow := sum_inv_primes_ge (by linarith) hP₁₂ hP₂pos hsubP hlogP₂
  have hθd := theta_sub_ge hCθ hθH hP₁2 hP₁₂
  have hgap := P₂_sub_P₁_ge hε hε1 hY
  have hlogP₁ := log_P₁_ge hε hε1 hY
  have hpow : (Real.log Y / 4) ^ 10 ≤ Real.log (P₁ ε Y) ^ 10 :=
    pow_le_pow_left₀ (by positivity) hlogP₁ 10
  have herr : 2 * Cθ * P₂ ε Y / Real.log (P₁ ε Y) ^ 10 ≤ ε / 34 * P₂ ε Y := by
    calc 2 * Cθ * P₂ ε Y / Real.log (P₁ ε Y) ^ 10 ≤ 2 * Cθ * P₂ ε Y / (Real.log Y / 4) ^ 10 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = 2 * 4 ^ 10 * Cθ / Real.log Y ^ 10 * P₂ ε Y := by
          rw [div_pow]; field_simp
      _ ≤ ε / 34 * P₂ ε Y := mul_le_mul_of_nonneg_right hθout hP₂pos.le
  have hθP : ε / 34 * P₂ ε Y ≤ Chebyshev.theta (P₂ ε Y) - Chebyshev.theta (P₁ ε Y) := by
    linarith
  have hlogle : Real.log (P₂ ε Y) ≤ Real.log Y :=
    Real.log_le_log hP₂pos (by nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ Y by linarith)])
  calc ε / (34 * Real.log Y) ≤ ε / (34 * Real.log (P₂ ε Y)) :=
        div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
    _ = ε / 34 * P₂ ε Y / (P₂ ε Y * Real.log (P₂ ε Y)) := by field_simp
    _ ≤ (Chebyshev.theta (P₂ ε Y) - Chebyshev.theta (P₁ ε Y)) /
          (P₂ ε Y * Real.log (P₂ ε Y)) := div_le_div_of_nonneg_right hθP (by positivity)
    _ ≤ _ := hlow

/-- The inner bound for one prime `p`. -/
theorem inner_primesP_ge {Cθ : ℝ} (hCθ : 0 ≤ Cθ)
    (hθH : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ Cθ * x / Real.log x ^ 10)
    (hwin : (1 - ε / 8) * Y ≤ (Y - 1) * Real.exp (-(3 * Θs Y / 4)))
    (hθin : 2 ^ 11 * Cθ / Real.log Y ^ 10 ≤ Θs Y / 8)
    {v : ℝ} (hv1 : Real.log (Y - 1) ≤ v) (hv2 : v ≤ Real.log ((1 + ε / 8) * Y))
    {p : ℕ} (hp : p ∈ primesP ε Y) :
    bumpMid / (8 * Real.log Y) * (1 / (p : ℝ)) ≤
      ∑ k ∈ primesK Y, 1 / ((p : ℝ) * k) *
        ((Θs Y)⁻¹ * bump ((v - (Real.log p + Real.log k)) / Θs Y)) := by
  have hL2 := logY_ge_two hε hε1 hY
  have hs4 := sqrtY_ge hε hε1 hY
  have hΘ : 0 < Θs Y := Θs_pos hε hε1 hY
  have hΘ1 : Θs Y ≤ 1 := by
    rw [Θs, div_le_one (by positivity)]
    exact one_le_pow₀ (by linarith)
  have hexpv1 : Y - 1 ≤ Real.exp v := by
    rw [← Real.exp_log (show (0 : ℝ) < Y - 1 by linarith)]; exact Real.exp_le_exp.mpr hv1
  have hexpv2 : Real.exp v ≤ (1 + ε / 8) * Y := by
    rw [← Real.exp_log (show (0 : ℝ) < (1 + ε / 8) * Y by positivity)]
    exact Real.exp_le_exp.mpr hv2
  obtain ⟨hpprime, hpP₁, hpP₂⟩ := mem_primesP hε hε1 hY hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hP₁ := P₁_ge hε hε1 hY
  have hsm := sqrt_mul_le hε hε1 hY
  -- the window endpoints
  have hAB : Real.exp (v - 3 * Θs Y / 4) / p =
      Real.exp (v - Θs Y / 4) / p * Real.exp (-(Θs Y / 2)) := by
    rw [div_mul_eq_mul_div, ← Real.exp_add]; congr 2; ring
  have hAge : √Y ≤ Real.exp (v - 3 * Θs Y / 4) / p := by
    rw [le_div_iff₀ hp0]
    have h1 : Real.exp (v - 3 * Θs Y / 4) = Real.exp v * Real.exp (-(3 * Θs Y / 4)) := by
      rw [← Real.exp_add]; congr 1
    rw [h1]
    have h2 : (1 - ε / 8) * Y ≤ Real.exp v * Real.exp (-(3 * Θs Y / 4)) :=
      hwin.trans (mul_le_mul_of_nonneg_right hexpv1 (Real.exp_pos _).le)
    have h3 : √Y * p ≤ √Y * P₂ ε Y := mul_le_mul_of_nonneg_left hpP₂ (by positivity)
    have h4 : √Y * P₂ ε Y = (1 - ε / 8) * Y := by
      unfold P₂
      have hss := Real.mul_self_sqrt (show (0 : ℝ) ≤ Y by linarith)
      linear_combination (1 - ε / 8) * hss
    linarith
  have hBle : Real.exp (v - Θs Y / 4) / p ≤ 3 * √Y := by
    rw [div_le_iff₀ hp0]
    have h1 : Real.exp (v - Θs Y / 4) ≤ Real.exp v := Real.exp_le_exp.mpr (by linarith)
    have h2 : (1 + ε / 8) * Y = √((1 + ε / 8) * Y) * √((1 + ε / 8) * Y) :=
      (Real.mul_self_sqrt (by positivity)).symm
    have h3 : 3 * √Y * P₁ ε Y ≤ 3 * √Y * p := mul_le_mul_of_nonneg_left hpP₁ (by positivity)
    have h5 : √((1 + ε / 8) * Y) * √((1 + ε / 8) * Y) ≤ 3 * √Y * P₁ ε Y := by
      unfold P₁
      have h6 : √((1 + ε / 8) * Y) ≤ 3 * √Y * (1 - ε / 4) := by nlinarith
      have h7 := Real.sqrt_nonneg ((1 + ε / 8) * Y)
      calc √((1 + ε / 8) * Y) * √((1 + ε / 8) * Y)
          ≤ 3 * √Y * (1 - ε / 4) * √((1 + ε / 8) * Y) := mul_le_mul_of_nonneg_right h6 h7
        _ = 3 * √Y * ((1 - ε / 4) * √((1 + ε / 8) * Y)) := by ring
    linarith
  have hAleB : Real.exp (v - 3 * Θs Y / 4) / p ≤ Real.exp (v - Θs Y / 4) / p := by
    rw [hAB]
    exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by linarith))
  have hA2 : 2 ≤ Real.exp (v - 3 * Θs Y / 4) / p := by linarith
  have hB1 : 1 < Real.exp (v - Θs Y / 4) / p := by linarith
  refine inner_ge hpprime.pos hΘ ?_ ?_ hB1 ?_
  · -- the window lies in `primesK`
    intro k hk
    simp only [mem_filter, mem_Ioc] at hk
    have hkA : Real.exp (v - 3 * Θs Y / 4) / p < k := by
      have := Nat.lt_floor_add_one (Real.exp (v - 3 * Θs Y / 4) / p)
      have h2 : ((⌊Real.exp (v - 3 * Θs Y / 4) / p⌋₊ : ℕ) : ℝ) + 1 ≤ k := by
        exact_mod_cast hk.1.1
      linarith
    simp only [primesK, mem_filter, mem_Icc]
    refine ⟨⟨Nat.ceil_le.mpr (by linarith), ?_⟩, hk.2⟩
    exact hk.1.2.trans (Nat.floor_le_floor hBle)
  · -- `θ(B) - θ(A) ≥ Θ B / 8`
    have hsub := theta_sub_ge hCθ hθH hA2 hAleB
    have hdiff : Θs Y / 4 * (Real.exp (v - Θs Y / 4) / p) ≤
        Real.exp (v - Θs Y / 4) / p - Real.exp (v - 3 * Θs Y / 4) / p := by
      rw [hAB]
      have h := one_sub_exp_neg_ge (x := Θs Y / 2) (by positivity) (by linarith)
      have hB0 : 0 ≤ Real.exp (v - Θs Y / 4) / p := by positivity
      have := mul_le_mul_of_nonneg_left h hB0
      linarith
    have hlogA : Real.log Y / 2 ≤ Real.log (Real.exp (v - 3 * Θs Y / 4) / p) := by
      rw [← log_sqrt_eq hε hε1 hY]
      exact Real.log_le_log (by positivity) hAge
    have hpow : (Real.log Y / 2) ^ 10 ≤ Real.log (Real.exp (v - 3 * Θs Y / 4) / p) ^ 10 :=
      pow_le_pow_left₀ (by positivity) hlogA 10
    have hB0 : 0 ≤ Real.exp (v - Θs Y / 4) / p := by positivity
    have herr : 2 * Cθ * (Real.exp (v - Θs Y / 4) / p) /
        Real.log (Real.exp (v - 3 * Θs Y / 4) / p) ^ 10 ≤
          Θs Y / 8 * (Real.exp (v - Θs Y / 4) / p) := by
      calc 2 * Cθ * (Real.exp (v - Θs Y / 4) / p) /
            Real.log (Real.exp (v - 3 * Θs Y / 4) / p) ^ 10
          ≤ 2 * Cθ * (Real.exp (v - Θs Y / 4) / p) / (Real.log Y / 2) ^ 10 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
        _ = 2 ^ 11 * Cθ / Real.log Y ^ 10 * (Real.exp (v - Θs Y / 4) / p) := by
            rw [div_pow]; field_simp
        _ ≤ Θs Y / 8 * (Real.exp (v - Θs Y / 4) / p) := mul_le_mul_of_nonneg_right hθin hB0
    linarith
  · exact Real.log_le_log (by positivity)
      (hBle.trans (by nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ Y by linarith)]))

/-- **The long-average lower bound.** -/
theorem Fr_long_ge {Cθ : ℝ} (hCθ : 0 ≤ Cθ)
    (hθH : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ Cθ * x / Real.log x ^ 10)
    (hwin : (1 - ε / 8) * Y ≤ (Y - 1) * Real.exp (-(3 * Θs Y / 4)))
    (hθin : 2 ^ 11 * Cθ / Real.log Y ^ 10 ≤ Θs Y / 8)
    (hθout : 2 * 4 ^ 10 * Cθ / Real.log Y ^ 10 ≤ ε / 34)
    {v : ℝ} (hv1 : Real.log (Y - 1) ≤ v) (hv2 : v ≤ Real.log ((1 + ε / 8) * Y)) :
    bumpMid * ε / (272 * Real.log Y ^ 2) ≤ Fr (primesP ε Y) (primesK Y) (Θs Y) v := by
  have hL2 := logY_ge_two hε hε1 hY
  have hFr := Fr_ge (Ps := primesP ε Y) (Ks := primesK Y) (Θ := Θs Y) (v := v)
    (L := Real.log Y) (fun p hp => inner_primesP_ge hε hε1 hY hCθ hθH hwin hθin hv1 hv2 hp)
  have hsum := sum_inv_primesP_ge hε hε1 hY hCθ hθH hθout
  have hbm := bumpMid_pos
  calc bumpMid * ε / (272 * Real.log Y ^ 2) =
        bumpMid / (8 * Real.log Y) * (ε / (34 * Real.log Y)) := by
        field_simp; ring
    _ ≤ bumpMid / (8 * Real.log Y) * ∑ p ∈ primesP ε Y, (1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := hFr

end LongAvg

end Erdos430Sqrt
