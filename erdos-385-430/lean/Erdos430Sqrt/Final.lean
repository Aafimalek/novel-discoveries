import Erdos430Sqrt.Block

/-!
# Erdős Problem 385, the `√n` scale for almost all `n` (conditional)

`sqrt_almost_all`: assuming `MeanValueHyp`, `ThetaHyp` and `PrimeSumHyp`, for every `ε > 0`
the integers `n` with `F n < n + (1 - ε) √n` have natural density zero.
-/

open MeasureTheory Complex Real Finset Filter
open scoped Topology

noncomputable section

namespace Erdos430Sqrt

/-! ### Eventual inequalities -/

theorem eventually_log_pow_le_sqrt (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ Y : ℝ in atTop, Real.log Y ^ k ≤ c * √Y := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound hc
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with Y hY hY1
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    Real.rpow_natCast, ← Real.sqrt_eq_rpow] at hY
  exact hY

theorem eventually_le_log_pow (k : ℕ) (hk : k ≠ 0) (c : ℝ) :
    ∀ᶠ Y : ℝ in atTop, c ≤ Real.log Y ^ k :=
  ((tendsto_pow_atTop hk).comp Real.tendsto_log_atTop).eventually_ge_atTop c

theorem eventually_le_sqrt (c : ℝ) : ∀ᶠ Y : ℝ in atTop, c ≤ √Y :=
  Real.tendsto_sqrt_atTop.eventually_ge_atTop c

/-- All the size conditions of `card_badBlock_le` hold for large `Y`. -/
theorem eventually_conditions {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {Cθ : ℝ} (hCθ : 0 ≤ Cθ) :
    ∀ᶠ Y : ℝ in atTop, 16 ≤ Y ∧ θs ε Y ≤ Θs Y ∧
      2 * π * (Real.log Y ^ 2 / θs ε Y) ≤ Y ^ 2 ∧ 6 * Real.log Y ^ 3 ≤ √Y ∧
      (1 - ε / 8) * Y ≤ (Y - 1) * Real.exp (-(3 * Θs Y / 4)) ∧
      2 ^ 11 * Cθ / Real.log Y ^ 10 ≤ Θs Y / 8 ∧
      2 * 4 ^ 10 * Cθ / Real.log Y ^ 10 ≤ ε / 34 ∧ 1 ≤ ε * √Y / 16 := by
  filter_upwards [eventually_ge_atTop (16 : ℝ), eventually_ge_atTop (64 * π / ε),
    eventually_ge_atTop (16 / ε),
    eventually_log_pow_le_sqrt 6 (show (0 : ℝ) < 32 / ε by positivity),
    eventually_log_pow_le_sqrt 2 one_pos,
    eventually_log_pow_le_sqrt 3 (show (0 : ℝ) < 1 / 6 by norm_num),
    eventually_le_log_pow 6 (by norm_num) (12 / ε),
    eventually_le_log_pow 4 (by norm_num) (2 ^ 14 * Cθ),
    eventually_le_log_pow 10 (by norm_num) (68 * 4 ^ 10 * Cθ / ε),
    eventually_le_sqrt (16 / ε)] with Y h16 hπ hYε h6 h2 h3 hΘε hin hout hsq
  have hY0 : 0 < Y := by linarith
  have hs : 0 < √Y := Real.sqrt_pos.mpr hY0
  have hss : √Y * √Y = Y := Real.mul_self_sqrt hY0.le
  have hL1 : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hY0]; have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < Real.log Y := by linarith
  refine ⟨h16, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `θ ≤ Θ`
    unfold θs Θs
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ε * Real.log Y ^ 6 ≤ 32 * √Y := by
      have := mul_le_mul_of_nonneg_left h6 hε.le
      calc ε * Real.log Y ^ 6 ≤ ε * (32 / ε * √Y) := this
        _ = 32 * √Y := by field_simp
    linarith
  · -- `2π Z ≤ Y²`
    unfold θs
    have hZ : Real.log Y ^ 2 / (ε / (32 * √Y)) = Real.log Y ^ 2 * (32 * √Y) / ε := by
      field_simp
    rw [hZ]
    have h1 : Real.log Y ^ 2 * (32 * √Y) ≤ √Y * (32 * √Y) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : √Y * (32 * √Y) = 32 * Y := by linear_combination 32 * hss
    have h3 : 2 * π * (Real.log Y ^ 2 * (32 * √Y) / ε) ≤ 2 * π * (32 * Y / ε) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (h1.trans h2.le) hε.le
    refine h3.trans ?_
    have : 64 * π * Y / ε ≤ Y * Y := by
      rw [div_le_iff₀ hε]
      have := mul_le_mul_of_nonneg_right hπ (show 0 ≤ Y * ε by positivity)
      calc 64 * π * Y = 64 * π / ε * (Y * ε) := by field_simp
        _ ≤ Y * (Y * ε) := this
        _ = Y * Y * ε := by ring
    calc 2 * π * (32 * Y / ε) = 64 * π * Y / ε := by ring
      _ ≤ Y * Y := this
      _ = Y ^ 2 := by ring
  · -- `6 (log Y)³ ≤ √Y`
    linarith
  · -- the window condition
    unfold Θs
    have hΘ : 1 / Real.log Y ^ 6 ≤ ε / 12 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := mul_le_mul_of_nonneg_left hΘε hε.le
      calc 1 * 12 = ε * (12 / ε) := by field_simp
        _ ≤ ε * Real.log Y ^ 6 := this
    have hexp : 1 - 3 * (1 / Real.log Y ^ 6) / 4 ≤ Real.exp (-(3 * (1 / Real.log Y ^ 6) / 4)) := by
      linarith [Real.add_one_le_exp (-(3 * (1 / Real.log Y ^ 6) / 4))]
    have hY1 : 1 ≤ ε * Y / 16 := by
      rw [le_div_iff₀ (by norm_num)]
      have := mul_le_mul_of_nonneg_left hYε hε.le
      calc 1 * 16 = ε * (16 / ε) := by field_simp
        _ ≤ ε * Y := this
    have hYm : 0 ≤ Y - 1 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hexp hYm
    have hΘ0 : 0 ≤ 1 / Real.log Y ^ 6 := by positivity
    have h2 : 3 * (1 / Real.log Y ^ 6) / 4 * Y ≤ ε * Y / 16 := by
      have := mul_le_mul_of_nonneg_right hΘ hY0.le
      nlinarith
    nlinarith
  · -- the inner `θ` error
    unfold Θs
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : 2 ^ 11 * Cθ * (Real.log Y ^ 6 * 8) = 2 ^ 14 * Cθ * Real.log Y ^ 6 := by ring
    have e2 : 1 * Real.log Y ^ 10 = Real.log Y ^ 4 * Real.log Y ^ 6 := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hin (by positivity)
  · -- the outer `θ` error
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hout hε.le
    have h1 : ε * (68 * 4 ^ 10 * Cθ / ε) = 2 * 4 ^ 10 * Cθ * 34 := by field_simp; ring
    linarith
  · -- `h ≥ 2`
    rw [le_div_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left hsq hε.le
    calc 1 * 16 = ε * (16 / ε) := by field_simp
      _ ≤ ε * √Y := this

/-! ### The block bound for large `Y` -/

theorem eventually_card_badBlock_le (hMV : MeanValueHyp) (hθ : ThetaHyp) (hPS : PrimeSumHyp)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ Y : ℝ in atTop, ((badBlock ε Y).card : ℝ) ≤ δ * Y := by
  obtain ⟨CMV, hCMV, hMV'⟩ := hMV
  obtain ⟨Cθ, hCθ, hθ'⟩ := hθ
  obtain ⟨CH, Y₀, hPS'⟩ := hPS
  obtain ⟨Cφ, -, hCφ⟩ := bumpHat_decay
  set K := K₁ ε CMV CH Cφ with hK
  have hbm := bumpMid_pos
  filter_upwards [eventually_conditions hε hε1 hCθ, eventually_ge_atTop Y₀,
    eventually_le_log_pow 2 (by norm_num) (2 * 272 ^ 2 * |K| / (bumpMid ^ 2 * ε ^ 2) / δ)]
    with Y hc hY₀ hlog
  obtain ⟨h16, hθΘ, hZ, hT, hwin, hθin, hθout, hh⟩ := hc
  have hcard := card_badBlock_le hε hε1 h16 hCMV (fun N b T hT => hMV' N b T hT) (hPS' Y hY₀)
    hCφ hCθ hθ' hθΘ hZ hT hwin hθin hθout hh
  have hY0 : 0 < Y := by linarith
  have hL1 : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hY0]; have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < Real.log Y := by linarith
  refine hcard.trans ?_
  have heq : 2 * Y * (K / Real.log Y ^ 6) / (bumpMid * ε / (272 * Real.log Y ^ 2)) ^ 2 =
      2 * 272 ^ 2 * K / (bumpMid ^ 2 * ε ^ 2) / Real.log Y ^ 2 * Y := by
    first | (field_simp; done) | (field_simp; ring)
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ hY0.le
  rw [div_le_iff₀ (by positivity)]
  have hpos : 0 < bumpMid ^ 2 * ε ^ 2 := by positivity
  have h1 : 2 * 272 ^ 2 * K / (bumpMid ^ 2 * ε ^ 2) ≤ 2 * 272 ^ 2 * |K| / (bumpMid ^ 2 * ε ^ 2) :=
    div_le_div_of_nonneg_right (by nlinarith [le_abs_self K]) hpos.le
  have h2 : 2 * 272 ^ 2 * |K| / (bumpMid ^ 2 * ε ^ 2) ≤ δ * Real.log Y ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlog hδ.le
    calc 2 * 272 ^ 2 * |K| / (bumpMid ^ 2 * ε ^ 2)
        = δ * (2 * 272 ^ 2 * |K| / (bumpMid ^ 2 * ε ^ 2) / δ) := by field_simp
      _ ≤ δ * Real.log Y ^ 2 := this
  linarith

/-! ### From blocks to density -/

/-- The exceptional integers below `X`. -/
def badBelow (ε : ℝ) (X : ℕ) : Finset ℕ :=
  (range X).filter fun n => (Erdos430.F n : ℝ) < n + (1 - ε) * √n

theorem badBelow_subset {ε Y₁ q : ℝ} (hY₁ : 1 ≤ Y₁) (hq : 1 < q) {X : ℕ} {J : ℕ}
    (hX : (X : ℝ) ≤ Y₁ * q ^ (J + 1)) (hqε : q = 1 + ε / 8) :
    badBelow ε X ⊆ range ⌈Y₁⌉₊ ∪ (range (J + 1)).biUnion fun j => badBlock ε (Y₁ * q ^ j) := by
  intro n hn
  simp only [badBelow, mem_filter, mem_range] at hn
  rw [mem_union, mem_range]
  by_cases hsmall : n < ⌈Y₁⌉₊
  · left; exact hsmall
  right
  push Not at hsmall
  have hnY : Y₁ ≤ n := Nat.ceil_le.mp hsmall
  have hY0 : 0 < Y₁ := by linarith
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (show 1 ≤ (n : ℝ) / Y₁ by
    rw [le_div_iff₀ hY0]; linarith) hq
  rw [le_div_iff₀ hY0] at hj1
  rw [div_lt_iff₀ hY0] at hj2
  have hjJ : j < J + 1 := by
    have hlt : q ^ j < q ^ (J + 1) := by
      have h1 : Y₁ * q ^ j < Y₁ * q ^ (J + 1) := by
        have : (n : ℝ) < X := by exact_mod_cast hn.1
        nlinarith
      exact lt_of_mul_lt_mul_left h1 hY0.le
    exact (pow_lt_pow_iff_right₀ hq).mp hlt
  rw [mem_biUnion]
  refine ⟨j, mem_range.mpr hjJ, ?_⟩
  simp only [badBlock, mem_filter, mem_Icc]
  refine ⟨⟨Nat.ceil_le.mpr (by linarith), ?_⟩, hn.2⟩
  rw [← hqε, Nat.le_floor_iff (mul_nonneg (by linarith) (mul_nonneg hY0.le
    (pow_nonneg (by linarith) _)))]
  have : q ^ (j + 1) = q * q ^ j := by ring
  nlinarith

/-- **Conditional theorem.** Assuming the three classical inputs, for every `ε > 0` the
integers `n` with `F n < n + (1 - ε) √n` have natural density zero. -/
theorem sqrt_almost_all (hMV : MeanValueHyp) (hθ : ThetaHyp) (hPS : PrimeSumHyp)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun X : ℕ => ((badBelow ε X).card : ℝ) / X) atTop (𝓝 0) := by
  -- reduce to `ε ≤ 1`
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hsub : ∀ X, badBelow ε X ⊆ badBelow ε' X := by
    intro X n hn
    simp only [badBelow, mem_filter] at hn ⊢
    refine ⟨hn.1, hn.2.trans_le ?_⟩
    have : (1 - ε) * √(n : ℝ) ≤ (1 - ε') * √(n : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [min_le_left ε 1]) (Real.sqrt_nonneg _)
    linarith
  refine squeeze_zero (fun X => by positivity) (fun X => ?_) (?_ : Tendsto (fun X : ℕ =>
    ((badBelow ε' X).card : ℝ) / X) atTop (𝓝 0))
  · exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card (hsub X)) (by positivity)
  -- the main argument for `ε' ≤ 1`
  set q := 1 + ε' / 8 with hq
  have hq1 : 1 < q := by linarith
  rw [Metric.tendsto_atTop]
  intro η hη
  set δ := η * (q - 1) / (2 * q) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨Y₁', hY₁'⟩ := (eventually_card_badBlock_le hMV hθ hPS hε'0 hε'1 hδ0).exists_forall_of_atTop
  set Y₁ := max Y₁' 1 with hY₁
  have hY₁1 : 1 ≤ Y₁ := le_max_right _ _
  have hblock : ∀ Y, Y₁ ≤ Y → ((badBlock ε' Y).card : ℝ) ≤ δ * Y :=
    fun Y hY => hY₁' Y ((le_max_left _ _).trans hY)
  -- choose `X₀` so that `(Y₁ + 1) / X < η / 2` for `X ≥ X₀`
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt (2 * (Y₁ + 1) / η)
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hXge : X₀ ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  by_cases hXY : (X : ℝ) ≤ Y₁
  · -- small `X`: trivial bound
    have hcard : ((badBelow ε' X).card : ℝ) ≤ X := by
      have := card_le_card (filter_subset (fun n => (Erdos430.F n : ℝ) < n + (1 - ε') * √n)
        (range X))
      rw [card_range] at this
      exact_mod_cast this
    have hX0' : (X₀ : ℝ) ≤ X := by exact_mod_cast hXge
    have : 2 * (Y₁ + 1) / η < X := lt_of_lt_of_le hX₀ hX0'
    rw [div_lt_iff₀ hη] at this
    have hle1 : ((badBelow ε' X).card : ℝ) / X ≤ 1 := (div_le_one hXpos).mpr hcard
    by_cases hη1 : 1 < η
    · linarith
    · push Not at hη1
      exfalso
      have : (X : ℝ) * η ≤ X := mul_le_of_le_one_right hXpos.le hη1
      linarith
  push Not at hXY
  obtain ⟨J, hJ1, hJ2⟩ := exists_nat_pow_near (show 1 ≤ (X : ℝ) / Y₁ by
    rw [le_div_iff₀ (by linarith)]; linarith) hq1
  rw [le_div_iff₀ (by linarith)] at hJ1
  rw [div_lt_iff₀ (by linarith)] at hJ2
  have hsubset := badBelow_subset (ε := ε') hY₁1 hq1 (X := X) (J := J) (by linarith) hq
  have hcard : ((badBelow ε' X).card : ℝ) ≤ (⌈Y₁⌉₊ : ℝ) + ∑ j ∈ range (J + 1), δ * (Y₁ * q ^ j) := by
    have h1 := card_le_card hsubset
    have h2 := card_union_le (range ⌈Y₁⌉₊) ((range (J + 1)).biUnion fun j => badBlock ε' (Y₁ * q ^ j))
    have h3 := card_biUnion_le (s := range (J + 1)) (t := fun j => badBlock ε' (Y₁ * q ^ j))
    have h4 : ((badBelow ε' X).card : ℝ) ≤ (⌈Y₁⌉₊ : ℝ) +
        ∑ j ∈ range (J + 1), ((badBlock ε' (Y₁ * q ^ j)).card : ℝ) := by
      rw [card_range] at h2
      exact_mod_cast h1.trans (h2.trans (Nat.add_le_add_left h3 _))
    refine h4.trans (add_le_add (le_refl _) (sum_le_sum fun j _ => hblock _ ?_))
    exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ hq1.le)
  have hgeom : ∑ j ∈ range (J + 1), δ * (Y₁ * q ^ j) ≤ δ * (Y₁ * q ^ (J + 1) / (q - 1)) := by
    rw [← mul_sum, ← mul_sum]
    apply mul_le_mul_of_nonneg_left _ hδ0.le
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [geom_sum_eq hq1.ne', le_div_iff₀ (by linarith), div_mul_cancel₀ _ (by linarith)]
    linarith
  have hYJ : Y₁ * q ^ (J + 1) ≤ q * X := by
    have : q ^ (J + 1) = q * q ^ J := by ring
    rw [this]; nlinarith
  have hceil : (⌈Y₁⌉₊ : ℝ) ≤ Y₁ + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hX0' : (X₀ : ℝ) ≤ X := by exact_mod_cast hXge
  have hsmall : (Y₁ + 1) / X < η / 2 := by
    have : 2 * (Y₁ + 1) / η < X := lt_of_lt_of_le hX₀ hX0'
    rw [div_lt_iff₀ hη] at this
    rw [div_lt_iff₀ hXpos]; linarith
  have hbig : δ * (Y₁ * q ^ (J + 1) / (q - 1)) / X ≤ η / 2 := by
    rw [div_le_iff₀ hXpos]
    have : δ * (Y₁ * q ^ (J + 1) / (q - 1)) ≤ δ * (q * X / (q - 1)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hYJ (by linarith)) hδ0.le
    calc δ * (Y₁ * q ^ (J + 1) / (q - 1)) ≤ δ * (q * X / (q - 1)) := this
      _ = η / 2 * X := by rw [hδ]; first | (field_simp; done) | (field_simp; ring)
  calc ((badBelow ε' X).card : ℝ) / X ≤ ((Y₁ + 1) + δ * (Y₁ * q ^ (J + 1) / (q - 1))) / X :=
        div_le_div_of_nonneg_right (by linarith) hXpos.le
    _ = (Y₁ + 1) / X + δ * (Y₁ * q ^ (J + 1) / (q - 1)) / X := by rw [add_div]
    _ < η / 2 + η / 2 := add_lt_add_of_lt_of_le hsmall hbig
    _ = η := by ring

/-- The matching upper bound holds for every `n` and needs no hypotheses: a composite `m < n`
has `p(m)² ≤ m < n`. With `sqrt_almost_all` this gives `F n = n + (1 - o(1)) √n` for almost
all `n`. -/
theorem F_le_add_sqrt (n : ℕ) : (Erdos430.F n : ℝ) ≤ n + √n := by
  have h : Erdos430.F n ≤ n + Nat.sqrt n := by
    rw [Erdos430.F_le_iff]
    rintro x ⟨m, hmn, hm1, hmp, rfl⟩
    have hsq : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hmp
    have hle : m.minFac ≤ Nat.sqrt n := Nat.le_sqrt'.mpr (hsq.trans hmn.le)
    omega
  have h2 : (Nat.sqrt n : ℝ) ≤ √n := Real.nat_sqrt_le_real_sqrt
  have h3 : (Erdos430.F n : ℝ) ≤ n + (Nat.sqrt n : ℝ) := by exact_mod_cast h
  linarith

end Erdos430Sqrt

#print axioms Erdos430Sqrt.sqrt_almost_all
#print axioms Erdos430Sqrt.F_le_add_sqrt
