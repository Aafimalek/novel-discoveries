import Mathlib

/-!
# Bounding a weighted mean square of a product of two Dirichlet polynomials

`integral_le_of_bounds` bounds `∫ ‖P w‖² ‖K w‖² wt(w) dw` given

* a pointwise bound `‖P w‖ ≤ σP` everywhere and `‖P w‖ ≤ M` for `T₀ ≤ |w| ≤ Z`;
* a mean value bound `∫_{-R}^{R} ‖K w‖² ≤ A R + B`;
* weight bounds `wt ≤ W₀` on `|w| ≤ T₀`, `wt ≤ 4` everywhere, `wt ≤ C_d / (θ w)⁴`.

The proof splits the line into `|w| ≤ T₀`, `T₀ ≤ |w| ≤ Z`, dyadic shells above `Z`, and a tail
whose contribution is made arbitrarily small by dominated convergence.
-/

open MeasureTheory Set Filter Finset
open scoped Topology

noncomputable section

namespace Erdos430Sqrt

theorem integral_indicator_Icc_eq {g : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R) :
    ∫ w, (Icc (-R) R).indicator g w = ∫ w in -R..R, g w := by
  rw [integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc]

/-- Choice of a dyadic shell: for `Z ≤ |w|` there is `j` with `2^j Z ≤ |w| < 2^(j+1) Z`. -/
theorem exists_dyadic {Z w : ℝ} (hZ : 0 < Z) (hw : Z ≤ |w|) :
    ∃ j : ℕ, (2 : ℝ) ^ j * Z ≤ |w| ∧ |w| < (2 : ℝ) ^ (j + 1) * Z := by
  set n : ℕ := ⌊|w| / Z⌋₊ with hn
  have hq : 1 ≤ |w| / Z := (one_le_div hZ).mpr hw
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.le_floor (by exact_mod_cast hq)
  refine ⟨Nat.log 2 n, ?_, ?_⟩
  · have h1 : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h2 : (n : ℝ) ≤ |w| / Z := Nat.floor_le (by positivity)
    have := h1.trans h2
    push_cast at this
    rwa [le_div_iff₀ hZ] at this
  · have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have h2 : |w| / Z < n + 1 := Nat.lt_floor_add_one _
    have h3 : (n : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    have := h2.trans_le h3
    rwa [div_lt_iff₀ hZ] at this

theorem integral_le_of_bounds (P K : ℝ → ℂ) (wt : ℝ → ℝ)
    (hint : Integrable (fun w => ‖P w‖ ^ 2 * ‖K w‖ ^ 2 * wt w))
    (hK : Continuous K) (hwt0 : ∀ w, 0 ≤ wt w)
    {σP T₀ Z M A B W₀ Cd θ : ℝ} (hσP : ∀ w, ‖P w‖ ≤ σP)
    (hT₀ : 0 < T₀) (hT₀Z : T₀ ≤ Z) (hM : ∀ w, T₀ ≤ |w| → |w| ≤ Z → ‖P w‖ ≤ M)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hMVT : ∀ R, 0 ≤ R → ∫ w in -R..R, ‖K w‖ ^ 2 ≤ A * R + B)
    (hwt_small : ∀ w, |w| ≤ T₀ → wt w ≤ W₀) (hwt_all : ∀ w, wt w ≤ 4)
    (hθ : 0 < θ) (hCd : 0 ≤ Cd) (hwt_decay : ∀ w, w ≠ 0 → wt w ≤ Cd / (θ * w) ^ 4) :
    ∫ w, ‖P w‖ ^ 2 * ‖K w‖ ^ 2 * wt w ≤
      σP ^ 2 * W₀ * (A * T₀ + B) + 4 * M ^ 2 * (A * Z + B) +
        σP ^ 2 * Cd / (θ * Z) ^ 4 * (4 * A * Z + 2 * B) := by
  set f : ℝ → ℝ := fun w => ‖P w‖ ^ 2 * ‖K w‖ ^ 2 * wt w with hf
  set k : ℝ → ℝ := fun w => ‖K w‖ ^ 2 with hk
  have hZ : 0 < Z := hT₀.trans_le hT₀Z
  have hf0 : ∀ w, 0 ≤ f w := fun w => mul_nonneg (by positivity) (hwt0 w)
  have hσP0 : 0 ≤ σP := (norm_nonneg _).trans (hσP 0)
  have hkcont : Continuous k := (hK.norm).pow 2
  have hk0 : ∀ w, 0 ≤ k w := fun w => by positivity
  have hW₀ : 0 ≤ W₀ := (hwt0 0).trans (hwt_small 0 (by simp [hT₀.le]))
  -- integrability of the pieces
  have hkint : ∀ R : ℝ, Integrable ((Icc (-R) R).indicator k) := fun R =>
    (hkcont.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hkI : ∀ R, 0 ≤ R → ∫ w, (Icc (-R) R).indicator k w ≤ A * R + B := fun R hR => by
    rw [integral_indicator_Icc_eq hR]; exact hMVT R hR
  -- the dyadic coefficients
  set c : ℕ → ℝ := fun j => σP ^ 2 * Cd / (θ * ((2 : ℝ) ^ j * Z)) ^ 4 with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  -- tail sets
  set tail : ℕ → Set ℝ := fun J => {w | (2 : ℝ) ^ J * Z ≤ |w|} with htail
  have htail_meas : ∀ J, MeasurableSet (tail J) := fun J =>
    measurableSet_le measurable_const (measurable_id.abs)
  -- pointwise bound
  have hpt : ∀ (J : ℕ) (w : ℝ), f w ≤
      σP ^ 2 * W₀ * (Icc (-T₀) T₀).indicator k w + 4 * M ^ 2 * (Icc (-Z) Z).indicator k w +
        ∑ j ∈ range J, c j * (Icc (-((2 : ℝ) ^ (j + 1) * Z)) ((2 : ℝ) ^ (j + 1) * Z)).indicator k w +
          (tail J).indicator f w := by
    intro J w
    have hP2 : ‖P w‖ ^ 2 ≤ σP ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hσP w) 2
    have hrest : 0 ≤ ∑ j ∈ range J,
        c j * (Icc (-((2 : ℝ) ^ (j + 1) * Z)) ((2 : ℝ) ^ (j + 1) * Z)).indicator k w :=
      sum_nonneg fun j _ => mul_nonneg (hc0 j) (indicator_nonneg (fun x _ => hk0 x) w)
    have hi1 : 0 ≤ (Icc (-T₀) T₀).indicator k w := indicator_nonneg (fun x _ => hk0 x) w
    have hi2 : 0 ≤ (Icc (-Z) Z).indicator k w := indicator_nonneg (fun x _ => hk0 x) w
    have hi3 : 0 ≤ (tail J).indicator f w := indicator_nonneg (fun x _ => hf0 x) w
    by_cases h1 : |w| ≤ T₀
    · have hmem : w ∈ Icc (-T₀) T₀ := abs_le.mp h1
      rw [indicator_of_mem hmem]
      have : f w ≤ σP ^ 2 * W₀ * k w := by
        simp only [hf, hk]
        calc ‖P w‖ ^ 2 * ‖K w‖ ^ 2 * wt w ≤ σP ^ 2 * ‖K w‖ ^ 2 * W₀ := by
              gcongr
              · exact hwt0 w
              · exact hwt_small w h1
          _ = σP ^ 2 * W₀ * ‖K w‖ ^ 2 := by ring
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * M ^ 2) hi2]
    by_cases h2 : |w| ≤ Z
    · have hmem : w ∈ Icc (-Z) Z := abs_le.mp h2
      rw [indicator_of_mem hmem]
      have hPM : ‖P w‖ ≤ M := hM w (by linarith) h2
      have : f w ≤ 4 * M ^ 2 * k w := by
        simp only [hf, hk]
        have hPM2 : ‖P w‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hPM 2
        calc ‖P w‖ ^ 2 * ‖K w‖ ^ 2 * wt w ≤ M ^ 2 * ‖K w‖ ^ 2 * 4 := by
              gcongr
              · exact hwt0 w
              · exact hwt_all w
          _ = 4 * M ^ 2 * ‖K w‖ ^ 2 := by ring
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ σP ^ 2 * W₀) hi1]
    push_neg at h2
    by_cases h3 : (2 : ℝ) ^ J * Z ≤ |w|
    · rw [indicator_of_mem (show w ∈ tail J from h3)]
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ σP ^ 2 * W₀) hi1,
        mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * M ^ 2) hi2]
    push_neg at h3
    obtain ⟨j, hj1, hj2⟩ := exists_dyadic hZ h2.le
    have hjJ : j < J := by
      by_contra hjJ
      push_neg at hjJ
      have : (2 : ℝ) ^ J * Z ≤ (2 : ℝ) ^ j * Z :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hjJ) hZ.le
      linarith
    have hw0 : w ≠ 0 := by
      intro h; rw [h, abs_zero] at h2; linarith
    have hmem : w ∈ Icc (-((2 : ℝ) ^ (j + 1) * Z)) ((2 : ℝ) ^ (j + 1) * Z) :=
      abs_le.mp hj2.le
    have hterm : f w ≤ c j * (Icc (-((2 : ℝ) ^ (j + 1) * Z)) ((2 : ℝ) ^ (j + 1) * Z)).indicator k w := by
      rw [indicator_of_mem hmem]
      simp only [hf, hk, hc]
      have hdec := hwt_decay w hw0
      have hpos : 0 < θ * ((2 : ℝ) ^ j * Z) := by positivity
      have hmono : Cd / (θ * w) ^ 4 ≤ Cd / (θ * ((2 : ℝ) ^ j * Z)) ^ 4 := by
        apply div_le_div_of_nonneg_left hCd (by positivity)
        rw [show (θ * w) ^ 4 = (θ * |w|) ^ 4 by rw [mul_pow, mul_pow, pow_abs, abs_of_nonneg
          (by positivity : (0 : ℝ) ≤ w ^ 4)] ]
        · exact pow_le_pow_left₀ hpos.le (mul_le_mul_of_nonneg_left hj1 hθ.le) 4
      calc ‖P w‖ ^ 2 * ‖K w‖ ^ 2 * wt w ≤ σP ^ 2 * ‖K w‖ ^ 2 * (Cd / (θ * ((2 : ℝ) ^ j * Z)) ^ 4) := by
            gcongr
            · exact hwt0 w
            · exact hdec.trans hmono
        _ = σP ^ 2 * Cd / (θ * ((2 : ℝ) ^ j * Z)) ^ 4 * ‖K w‖ ^ 2 := by ring
    have hsingle := single_le_sum (f := fun j => c j *
      (Icc (-((2 : ℝ) ^ (j + 1) * Z)) ((2 : ℝ) ^ (j + 1) * Z)).indicator k w)
      (fun i _ => mul_nonneg (hc0 i) (indicator_nonneg (fun x _ => hk0 x) w)) (mem_range.mpr hjJ)
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ σP ^ 2 * W₀) hi1,
      mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * M ^ 2) hi2]
  -- integrate the pointwise bound for a fixed `J`
  have hstep : ∀ J : ℕ, ∫ w, f w ≤
      σP ^ 2 * W₀ * (A * T₀ + B) + 4 * M ^ 2 * (A * Z + B) +
        σP ^ 2 * Cd / (θ * Z) ^ 4 * (4 * A * Z + 2 * B) + ∫ w, (tail J).indicator f w := by
    intro J
    set g3 : ℝ → ℝ := fun w => ∑ j ∈ range J, c j *
        (Icc (-((2 : ℝ) ^ (j + 1) * Z)) ((2 : ℝ) ^ (j + 1) * Z)).indicator k w with hg3
    have hint1 : Integrable (fun w => σP ^ 2 * W₀ * (Icc (-T₀) T₀).indicator k w) :=
      (hkint T₀).const_mul _
    have hint2 : Integrable (fun w => 4 * M ^ 2 * (Icc (-Z) Z).indicator k w) :=
      (hkint Z).const_mul _
    have hint3 : Integrable g3 :=
      integrable_finsetSum _ fun j _ => (hkint _).const_mul _
    have hint4 : Integrable ((tail J).indicator f) := hint.indicator (htail_meas J)
    have hint12 : Integrable (fun w => σP ^ 2 * W₀ * (Icc (-T₀) T₀).indicator k w +
        4 * M ^ 2 * (Icc (-Z) Z).indicator k w) := hint1.add hint2
    have hint123 : Integrable (fun w => σP ^ 2 * W₀ * (Icc (-T₀) T₀).indicator k w +
        4 * M ^ 2 * (Icc (-Z) Z).indicator k w + g3 w) := hint12.add hint3
    have hint1234 : Integrable (fun w => σP ^ 2 * W₀ * (Icc (-T₀) T₀).indicator k w +
        4 * M ^ 2 * (Icc (-Z) Z).indicator k w + g3 w + (tail J).indicator f w) :=
      hint123.add hint4
    have h1 : ∫ w, f w ≤ ∫ w, (σP ^ 2 * W₀ * (Icc (-T₀) T₀).indicator k w +
        4 * M ^ 2 * (Icc (-Z) Z).indicator k w + g3 w + (tail J).indicator f w) :=
      integral_mono hint hint1234 (fun w => hpt J w)
    rw [integral_add hint123 hint4, integral_add hint12 hint3, integral_add hint1 hint2,
      integral_const_mul, integral_const_mul, hg3,
      integral_finsetSum _ (fun j _ => (hkint _).const_mul _)] at h1
    have hshell : ∑ j ∈ range J, ∫ w, c j *
        (Icc (-((2 : ℝ) ^ (j + 1) * Z)) ((2 : ℝ) ^ (j + 1) * Z)).indicator k w ≤
        σP ^ 2 * Cd / (θ * Z) ^ 4 * (4 * A * Z + 2 * B) := by
      have hj : ∀ j ∈ range J, ∫ w, c j *
          (Icc (-((2 : ℝ) ^ (j + 1) * Z)) ((2 : ℝ) ^ (j + 1) * Z)).indicator k w ≤
          σP ^ 2 * Cd / (θ * Z) ^ 4 * ((1 / 16 : ℝ) ^ j * (2 * A * ((2 : ℝ) ^ j * Z)) +
            (1 / 16 : ℝ) ^ j * B) := by
        intro j _
        rw [integral_const_mul]
        have hI := hkI ((2 : ℝ) ^ (j + 1) * Z) (by positivity)
        have hcj : c j = σP ^ 2 * Cd / (θ * Z) ^ 4 * (1 / 16 : ℝ) ^ j := by
          simp only [hc]
          rw [show θ * ((2 : ℝ) ^ j * Z) = (2 : ℝ) ^ j * (θ * Z) by ring, mul_pow, ← pow_mul,
            show (1 / 16 : ℝ) ^ j = ((2 : ℝ) ^ (j * 4))⁻¹ by
              rw [div_pow, one_pow, pow_mul', one_div]; norm_num]
          field_simp
        rw [hcj]
        have hpos : 0 ≤ σP ^ 2 * Cd / (θ * Z) ^ 4 * (1 / 16 : ℝ) ^ j := by positivity
        calc σP ^ 2 * Cd / (θ * Z) ^ 4 * (1 / 16 : ℝ) ^ j *
              ∫ w, (Icc (-((2 : ℝ) ^ (j + 1) * Z)) ((2 : ℝ) ^ (j + 1) * Z)).indicator k w
            ≤ σP ^ 2 * Cd / (θ * Z) ^ 4 * (1 / 16 : ℝ) ^ j *
                (A * ((2 : ℝ) ^ (j + 1) * Z) + B) := mul_le_mul_of_nonneg_left hI hpos
          _ = _ := by ring
      refine (sum_le_sum hj).trans ?_
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [sum_add_distrib, ← sum_mul]
      have hgeo1 : ∑ j ∈ range J, (1 / 16 : ℝ) ^ j * (2 * A * ((2 : ℝ) ^ j * Z)) =
          2 * A * Z * ∑ j ∈ range J, (1 / 8 : ℝ) ^ j := by
        rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
        rw [show (1 / 8 : ℝ) ^ j = (1 / 16 : ℝ) ^ j * (2 : ℝ) ^ j by
          rw [← mul_pow]; norm_num]
        ring
      have hs8 : ∑ j ∈ range J, (1 / 8 : ℝ) ^ j ≤ 2 := by
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) (x := (1 / 8 : ℝ)) (by norm_num)
          (by norm_num)
        rw [← range_eq_Ico] at this
        refine this.trans ?_
        norm_num
      have hs16 : ∑ j ∈ range J, (1 / 16 : ℝ) ^ j ≤ 2 := by
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) (x := (1 / 16 : ℝ)) (by norm_num)
          (by norm_num)
        rw [← range_eq_Ico] at this
        refine this.trans ?_
        norm_num
      rw [hgeo1]
      nlinarith [mul_le_mul_of_nonneg_left hs8 (by positivity : (0 : ℝ) ≤ 2 * A * Z),
        mul_le_mul_of_nonneg_right hs16 hB]
    have hT := hkI T₀ hT₀.le
    have hZ' := hkI Z hZ.le
    nlinarith [mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ σP ^ 2 * W₀),
      mul_le_mul_of_nonneg_left hZ' (by positivity : (0 : ℝ) ≤ 4 * M ^ 2)]
  -- the tail tends to zero
  have htail0 : Tendsto (fun J : ℕ => ∫ w, (tail J).indicator f w) atTop (𝓝 0) := by
    have hlim : ∀ w, Tendsto (fun J : ℕ => (tail J).indicator f w) atTop (𝓝 0) := by
      intro w
      have hev : ∀ᶠ J : ℕ in atTop, (tail J).indicator f w = 0 := by
        have h2J : Tendsto (fun J : ℕ => (2 : ℝ) ^ J * Z) atTop atTop :=
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).atTop_mul_const hZ
        filter_upwards [h2J.eventually_gt_atTop |w|] with J hJ
        exact indicator_of_notMem (show w ∉ tail J from not_le.mpr hJ) _
      exact tendsto_const_nhds.congr' (hev.mono fun J h => h.symm)
    have := tendsto_integral_of_dominated_convergence (fun w => f w)
      (fun J => (hint.indicator (htail_meas J)).aestronglyMeasurable) hint
      (fun J => Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun x _ => hf0 x) w)]
        exact indicator_le_self' (fun x _ => hf0 x) w)
      (Eventually.of_forall hlim)
    simpa using this
  -- conclude
  apply le_of_forall_pos_lt_add
  intro δ hδ
  obtain ⟨J, hJ⟩ := (htail0.eventually (gt_mem_nhds hδ)).exists
  exact (hstep J).trans_lt (by linarith)

end Erdos430Sqrt
