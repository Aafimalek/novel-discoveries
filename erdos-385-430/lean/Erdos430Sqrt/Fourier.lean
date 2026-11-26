import Mathlib

/-!
# The smoothing function and the Plancherel identity

`bump` is a smooth nonnegative function supported in `(0, 1)` with integral `1`, and
`bumpHat` is its Fourier transform (mathlib's convention `𝓕 f w = ∫ e(-v w) f v dv`, with
`e(x) = exp (2 π i x)`). For a finite family of weights `c i` and positions `ℓ i`, the
smoothed count at scale `ϑ` is `∑ c i ϑ⁻¹ bump ((v - ℓ i) / ϑ)`. The Plancherel identity
`integral_norm_sq_D` expresses the mean square of the difference of two such counts through
the Dirichlet polynomial `∑ c i e(-ℓ i w)`.
-/

open MeasureTheory Complex Real Finset
open scoped FourierTransform SchwartzMap

noncomputable section

namespace Erdos430Sqrt

/-- The bump function: centre `1/2`, equal to a constant on `[1/4, 3/4]`, supported in `(0,1)`. -/
def bumpData : ContDiffBump (1 / 2 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The smoothing function, normalised to have integral `1`. -/
def bump : ℝ → ℝ := bumpData.normed volume

theorem bump_nonneg (x : ℝ) : 0 ≤ bump x := bumpData.nonneg_normed x

theorem bump_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bump := bumpData.contDiff_normed

theorem bump_integral : ∫ x, bump x = 1 := bumpData.integral_normed

theorem bump_continuous : Continuous bump := bump_contDiff.continuous

theorem bump_hasCompactSupport : HasCompactSupport bump := bumpData.hasCompactSupport_normed

theorem bump_integrable : Integrable bump := bumpData.integrable_normed

/-- `bump` vanishes outside `(0, 1)`. -/
theorem bump_mem_of_ne_zero {x : ℝ} (h : bump x ≠ 0) : 0 < x ∧ x < 1 := by
  have hx : x ∈ Function.support bump := h
  rw [bump, bumpData.support_normed_eq, Metric.mem_ball, Real.dist_eq] at hx
  have hr : bumpData.rOut = 1 / 2 := rfl
  rw [hr] at hx
  constructor <;> linarith [abs_lt.mp hx]

theorem bump_eq_zero_of_not_mem {x : ℝ} (h : x ≤ 0 ∨ 1 ≤ x) : bump x = 0 := by
  by_contra hne
  have := bump_mem_of_ne_zero hne
  rcases h with h | h <;> linarith [this.1, this.2]

/-- The constant value of `bump` on `[1/4, 3/4]`. -/
def bumpMid : ℝ := (∫ x, bumpData x)⁻¹

theorem bumpMid_pos : 0 < bumpMid := inv_pos.mpr bumpData.integral_pos

theorem bump_mid {x : ℝ} (hx : 1 / 4 ≤ x ∧ x ≤ 3 / 4) : bump x = bumpMid := by
  have hball : x ∈ Metric.closedBall (1 / 2 : ℝ) bumpData.rIn := by
    have hr : bumpData.rIn = 1 / 4 := rfl
    rw [hr, Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  rw [bump, bumpData.normed_def, bumpData.one_of_mem_closedBall hball, bumpMid, one_div]

/-- The complexified bump. -/
def bumpC (x : ℝ) : ℂ := (bump x : ℂ)

theorem bumpC_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bumpC :=
  ofRealCLM.contDiff.comp bump_contDiff

theorem bumpC_hasCompactSupport : HasCompactSupport bumpC := by
  show HasCompactSupport (fun x => ((bump x : ℝ) : ℂ))
  exact bump_hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) (by simp)

theorem bumpC_integrable : Integrable bumpC := bump_integrable.ofReal

/-- The Fourier transform of the bump. -/
def bumpHat (ξ : ℝ) : ℂ := 𝓕 bumpC ξ

theorem fourier_eq_exp (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = ∫ v, Complex.exp (((-2 * π * v * w : ℝ) : ℂ) * I) * f v := by
  rw [Real.fourier_eq']
  congr 1
  ext v
  simp only [smul_eq_mul]
  congr 3
  rw [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem norm_bumpHat_le_one (ξ : ℝ) : ‖bumpHat ξ‖ ≤ 1 := by
  calc ‖bumpHat ξ‖ ≤ ∫ v, ‖bumpC v‖ := Real.norm_fourier_le_integral_norm _ _
    _ = ∫ v, bump v := by
        congr 1; ext v; simp [bumpC, Complex.norm_real, abs_of_nonneg (bump_nonneg v)]
    _ = 1 := bump_integral

theorem norm_bumpHat_sub_one_le (ξ : ℝ) : ‖bumpHat ξ - 1‖ ≤ 2 * π * |ξ| := by
  have hint : Integrable (fun v : ℝ => Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * I) * bumpC v) := by
    have h := (Real.fourierIntegral_convergent_iff (μ := volume) (f := bumpC) ξ).mpr
      bumpC_integrable
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    congr 2
    simp [mul_comm, mul_assoc, mul_left_comm]
  have hone : (1 : ℂ) = ∫ v, bumpC v := by
    rw [show (fun v => bumpC v) = fun v => ((bump v : ℝ) : ℂ) from rfl, integral_complex_ofReal,
      bump_integral]
    simp
  rw [bumpHat, fourier_eq_exp, hone, ← integral_sub hint bumpC_integrable]
  calc ‖∫ v, (Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * I) * bumpC v - bumpC v)‖
      ≤ ∫ v, ‖Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * I) * bumpC v - bumpC v‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ v, 2 * π * |ξ| * bump v := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          ((bump_integrable).const_mul _)
        refine Filter.Eventually.of_forall fun v => ?_
        dsimp only
        rw [← sub_one_mul, norm_mul]
        by_cases hv : bump v = 0
        · simp [bumpC, hv]
        obtain ⟨h0, h1⟩ := bump_mem_of_ne_zero hv
        have hexp : ‖Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * I) - 1‖ ≤ 2 * π * |ξ| := by
          rw [mul_comm]
          refine (norm_exp_I_mul_ofReal_sub_one_le).trans ?_
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
            abs_two, abs_of_pos h0]
          have : 2 * π * v * |ξ| ≤ 2 * π * 1 * |ξ| := by gcongr
          linarith
        have hb : ‖bumpC v‖ = bump v := by
          simp [bumpC, Complex.norm_real, abs_of_nonneg (bump_nonneg v)]
        rw [hb]
        exact mul_le_mul_of_nonneg_right hexp (bump_nonneg v)
    _ = 2 * π * |ξ| := by rw [integral_const_mul, bump_integral, mul_one]

/-- Quadratic decay of the Fourier transform of the bump. -/
theorem bumpHat_decay : ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ξ ^ 2 * ‖bumpHat ξ‖ ≤ C := by
  let S : 𝓢(ℝ, ℂ) := bumpC_hasCompactSupport.toSchwartzMap bumpC_contDiff
  obtain ⟨C, hC, hdecay⟩ := (𝓕 S).decay 2 0
  refine ⟨C, hC, fun ξ => ?_⟩
  have h := hdecay ξ
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, sq_abs] at h
  have hS : (𝓕 S) ξ = bumpHat ξ := by
    rw [SchwartzMap.fourier_coe]
    rfl
  rwa [hS] at h

/-! ### Scaled translates and their Fourier transforms -/

/-- `ϑ⁻¹ bump ((v - ℓ) / ϑ)`, as a complex number. -/
def bumpAt (ϑ ℓ v : ℝ) : ℂ := ((ϑ⁻¹ * bump ((v - ℓ) / ϑ) : ℝ) : ℂ)

theorem bumpAt_continuous (ϑ ℓ : ℝ) : Continuous (bumpAt ϑ ℓ) := by
  unfold bumpAt
  exact continuous_ofReal.comp (continuous_const.mul
    (bump_continuous.comp ((continuous_id.sub continuous_const).div_const _)))

theorem bumpAt_contDiff (ϑ ℓ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bumpAt ϑ ℓ) := by
  unfold bumpAt
  apply ofRealCLM.contDiff.comp
  exact contDiff_const.mul (bump_contDiff.comp ((contDiff_id.sub contDiff_const).div_const _))

theorem bumpAt_eq_zero {ϑ ℓ v : ℝ} (hϑ : 0 < ϑ) (hv : v ≤ ℓ ∨ ℓ + ϑ ≤ v) : bumpAt ϑ ℓ v = 0 := by
  unfold bumpAt
  rw [bump_eq_zero_of_not_mem]
  · simp
  rcases hv with hv | hv
  · left; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hϑ.le
  · right; rw [le_div_iff₀ hϑ]; linarith

theorem bumpAt_integrable {ϑ ℓ : ℝ} (hϑ : 0 < ϑ) : Integrable (bumpAt ϑ ℓ) := by
  apply (bumpAt_continuous ϑ ℓ).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_Icc (a := ℓ) (b := ℓ + ϑ))
  intro v hv
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
  exact bumpAt_eq_zero hϑ (by rcases hv with h | h <;> [left; right] <;> linarith)

/-- The integrand of the Fourier transform of `bumpAt`. -/
def phaseBump (ϑ ℓ w v : ℝ) : ℂ := Complex.exp (((-2 * π * v * w : ℝ) : ℂ) * I) * bumpAt ϑ ℓ v

theorem fourier_bumpAt {ϑ : ℝ} (hϑ : 0 < ϑ) (ℓ w : ℝ) :
    𝓕 (bumpAt ϑ ℓ) w = Complex.exp (((-2 * π * ℓ * w : ℝ) : ℂ) * I) * bumpHat (ϑ * w) := by
  have h2 : ∫ v, phaseBump ϑ ℓ w (v + ℓ) = ϑ • ∫ x, phaseBump ϑ ℓ w (ϑ * x + ℓ) := by
    rw [Measure.integral_comp_mul_left (fun y => phaseBump ϑ ℓ w (y + ℓ)) ϑ, smul_smul,
      abs_of_pos (inv_pos.mpr hϑ), mul_inv_cancel₀ hϑ.ne', one_smul]
  have hpt : ∀ x : ℝ, ϑ • phaseBump ϑ ℓ w (ϑ * x + ℓ) =
      Complex.exp (((-2 * π * ℓ * w : ℝ) : ℂ) * I) *
        (Complex.exp (((-2 * π * x * (ϑ * w) : ℝ) : ℂ) * I) * bumpC x) := by
    intro x
    have hx : (ϑ * x + ℓ - ℓ) / ϑ = x := by field_simp; ring
    have hexp : Complex.exp (((-2 * π * (ϑ * x + ℓ) * w : ℝ) : ℂ) * I) =
        Complex.exp (((-2 * π * ℓ * w : ℝ) : ℂ) * I) *
          Complex.exp (((-2 * π * x * (ϑ * w) : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hc : (ϑ : ℂ) ≠ 0 := by exact_mod_cast hϑ.ne'
    simp only [phaseBump, bumpAt, bumpC, hx, hexp, Complex.real_smul]
    push_cast
    field_simp
  calc 𝓕 (bumpAt ϑ ℓ) w = ∫ v, phaseBump ϑ ℓ w v := fourier_eq_exp _ _
    _ = ∫ v, phaseBump ϑ ℓ w (v + ℓ) := (integral_add_right_eq_self _ ℓ).symm
    _ = ϑ • ∫ x, phaseBump ϑ ℓ w (ϑ * x + ℓ) := h2
    _ = ∫ x, ϑ • phaseBump ϑ ℓ w (ϑ * x + ℓ) := (integral_smul _ _).symm
    _ = ∫ x, Complex.exp (((-2 * π * ℓ * w : ℝ) : ℂ) * I) *
          (Complex.exp (((-2 * π * x * (ϑ * w) : ℝ) : ℂ) * I) * bumpC x) := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = Complex.exp (((-2 * π * ℓ * w : ℝ) : ℂ) * I) * bumpHat (ϑ * w) := by
        rw [integral_const_mul, ← fourier_eq_exp]
        rfl

/-! ### The difference of two smoothed counts -/

variable {ι : Type*}

/-- The difference of the smoothed counts at scales `θ` and `Θ`. -/
def D (s : Finset ι) (c ℓ : ι → ℝ) (θ Θ v : ℝ) : ℂ :=
  ∑ i ∈ s, (c i : ℂ) * (bumpAt θ (ℓ i) v - bumpAt Θ (ℓ i) v)

/-- The Dirichlet polynomial `∑ c i e(-ℓ i w)`. -/
def dirichlet (s : Finset ι) (c ℓ : ι → ℝ) (w : ℝ) : ℂ :=
  ∑ i ∈ s, (c i : ℂ) * Complex.exp (((-2 * π * ℓ i * w : ℝ) : ℂ) * I)

theorem D_contDiff (s : Finset ι) (c ℓ : ι → ℝ) (θ Θ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (D s c ℓ θ Θ) := by
  unfold D
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul ((bumpAt_contDiff _ _).sub (bumpAt_contDiff _ _))

theorem D_hasCompactSupport (s : Finset ι) (c ℓ : ι → ℝ) {θ Θ : ℝ} (hθ : 0 < θ) (hΘ : 0 < Θ) :
    HasCompactSupport (D s c ℓ θ Θ) := by
  set R : ℝ := ∑ i ∈ s, |ℓ i| + θ + Θ with hR
  apply HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
  intro v hv
  unfold D
  apply Finset.sum_eq_zero
  intro i hi
  have hℓ : |ℓ i| ≤ ∑ j ∈ s, |ℓ j| := single_le_sum (fun j _ => abs_nonneg (ℓ j)) hi
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
  have key : ∀ ϑ, 0 < ϑ → ϑ ≤ θ + Θ → bumpAt ϑ (ℓ i) v = 0 := by
    intro ϑ hϑ hϑle
    apply bumpAt_eq_zero hϑ
    rcases hv with h | h
    · left; linarith [neg_abs_le (ℓ i)]
    · right; linarith [le_abs_self (ℓ i)]
  rw [key θ hθ (by linarith), key Θ hΘ (by linarith), sub_self, mul_zero]

theorem fourier_D (s : Finset ι) (c ℓ : ι → ℝ) {θ Θ : ℝ} (hθ : 0 < θ) (hΘ : 0 < Θ) (w : ℝ) :
    𝓕 (D s c ℓ θ Θ) w = dirichlet s c ℓ w * (bumpHat (θ * w) - bumpHat (Θ * w)) := by
  have hint : ∀ i ∈ s, Integrable (fun v => (c i : ℂ) * (bumpAt θ (ℓ i) v - bumpAt Θ (ℓ i) v)) :=
    fun i _ => ((bumpAt_integrable hθ).sub (bumpAt_integrable hΘ)).const_mul _
  have hlin : 𝓕 (D s c ℓ θ Θ) w =
      ∑ i ∈ s, (c i : ℂ) * (𝓕 (bumpAt θ (ℓ i)) w - 𝓕 (bumpAt Θ (ℓ i)) w) := by
    rw [fourier_eq_exp]
    simp_rw [D, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [fourier_eq_exp, fourier_eq_exp, ← integral_sub, ← integral_const_mul]
      · congr 1; ext v; ring
      · exact (Real.fourierIntegral_convergent_iff (f := bumpAt θ (ℓ i)) w).mpr
          (bumpAt_integrable hθ) |>.congr (Filter.Eventually.of_forall fun v => by
            simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
            congr 2; simp [mul_comm, mul_assoc, mul_left_comm])
      · exact (Real.fourierIntegral_convergent_iff (f := bumpAt Θ (ℓ i)) w).mpr
          (bumpAt_integrable hΘ) |>.congr (Filter.Eventually.of_forall fun v => by
            simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
            congr 2; simp [mul_comm, mul_assoc, mul_left_comm])
    · intro i hi
      have := (Real.fourierIntegral_convergent_iff (f := fun v =>
        (c i : ℂ) * (bumpAt θ (ℓ i) v - bumpAt Θ (ℓ i) v)) w).mpr (hint i hi)
      refine this.congr (Filter.Eventually.of_forall fun v => ?_)
      simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
      rw [← mul_assoc, ← mul_assoc]
      congr 2
      · congr 2; simp [mul_comm, mul_assoc, mul_left_comm]
  rw [hlin, dirichlet, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fourier_bumpAt hθ, fourier_bumpAt hΘ]
  ring

/-- **Plancherel.** The mean square of `D` equals the weighted mean square of the
Dirichlet polynomial. -/
theorem integral_norm_sq_D (s : Finset ι) (c ℓ : ι → ℝ) {θ Θ : ℝ} (hθ : 0 < θ) (hΘ : 0 < Θ) :
    ∫ v, ‖D s c ℓ θ Θ v‖ ^ 2 =
      ∫ w, ‖dirichlet s c ℓ w‖ ^ 2 * ‖bumpHat (θ * w) - bumpHat (Θ * w)‖ ^ 2 := by
  let S : 𝓢(ℝ, ℂ) := (D_hasCompactSupport s c ℓ hθ hΘ).toSchwartzMap (D_contDiff s c ℓ θ Θ)
  have hP := SchwartzMap.integral_norm_sq_fourier S
  have hS : ∀ w, (𝓕 S) w = 𝓕 (D s c ℓ θ Θ) w := fun w => by
    rw [SchwartzMap.fourier_coe]; rfl
  simp_rw [hS, fourier_D s c ℓ hθ hΘ, norm_mul, mul_pow] at hP
  rw [hP]
  rfl

end Erdos430Sqrt

namespace Erdos430Sqrt

variable {ι : Type*}

theorem D_continuous (s : Finset ι) (c ℓ : ι → ℝ) (θ Θ : ℝ) : Continuous (D s c ℓ θ Θ) :=
  (D_contDiff s c ℓ θ Θ).continuous

theorem integrable_norm_sq_D (s : Finset ι) (c ℓ : ι → ℝ) {θ Θ : ℝ} (hθ : 0 < θ) (hΘ : 0 < Θ) :
    Integrable (fun v => ‖D s c ℓ θ Θ v‖ ^ 2) := by
  apply Continuous.integrable_of_hasCompactSupport ((D_continuous s c ℓ θ Θ).norm.pow 2)
  exact (D_hasCompactSupport s c ℓ hθ hΘ).comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)

theorem integrable_fourier_side (s : Finset ι) (c ℓ : ι → ℝ) {θ Θ : ℝ} (hθ : 0 < θ)
    (hΘ : 0 < Θ) :
    Integrable (fun w => ‖dirichlet s c ℓ w‖ ^ 2 * ‖bumpHat (θ * w) - bumpHat (Θ * w)‖ ^ 2) := by
  let S : 𝓢(ℝ, ℂ) := (D_hasCompactSupport s c ℓ hθ hΘ).toSchwartzMap (D_contDiff s c ℓ θ Θ)
  have hint : Integrable (fun w => ‖(𝓕 S) w‖ ^ 2) :=
    ((𝓕 S).memLp (2 : ℕ) volume).integrable_norm_pow two_ne_zero
  refine hint.congr (Filter.Eventually.of_forall fun w => ?_)
  show ‖(𝓕 S) w‖ ^ 2 = _
  rw [SchwartzMap.fourier_coe]
  show ‖𝓕 (D s c ℓ θ Θ) w‖ ^ 2 = _
  rw [fourier_D s c ℓ hθ hΘ, norm_mul, mul_pow]

end Erdos430Sqrt
