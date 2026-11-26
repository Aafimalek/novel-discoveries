import Erdos430Sqrt.LongAvg

/-!
# Counting the exceptions in one block

For `Y` large, the integers `N ∈ [Y, (1 + ε/8) Y]` with `F N < N + (1 - ε) √N` number at most
`2 Y · (K₁ / (log Y)⁶) / L²`, where `L = bumpMid ε / (272 (log Y)²)`.
-/

open MeasureTheory Complex Real Finset

noncomputable section

namespace Erdos430Sqrt

/-- The exceptional integers in the block `[Y, (1 + ε/8) Y]`. -/
def badBlock (ε Y : ℝ) : Finset ℕ :=
  (Icc ⌈Y⌉₊ ⌊(1 + ε / 8) * Y⌋₊).filter fun N => (Erdos430.F N : ℝ) < N + (1 - ε) * √N

theorem inv_le_log_sub_log {N : ℝ} (hN : 2 ≤ N) : 1 / N ≤ Real.log N - Real.log (N - 1) := by
  have hN0 : 0 < N := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (N - 1) / N by
    apply div_pos <;> linarith)
  rw [Real.log_div (by linarith) hN0.ne'] at h
  have : (N - 1) / N - 1 = -(1 / N) := by field_simp; ring
  linarith

section Block

variable {ε Y : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hY : 16 ≤ Y)
include hε hε1 hY

theorem card_badBlock_le {CMV CH Cφ Cθ : ℝ} (hCMV : 0 ≤ CMV)
    (hMV : ∀ (N : ℕ) (b : ℕ → ℂ) (T : ℝ), 0 ≤ T →
      ∫ t in -T..T, mvSum N b t ≤ (2 * T + CMV * N) * ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2)
    (hPS : ∀ P₁ P₂ : ℝ, √Y / 4 ≤ P₁ → P₂ ≤ 4 * √Y → ∀ t : ℝ, 1 ≤ |t| → |t| ≤ Y ^ 2 →
      ‖∑ p ∈ (Icc ⌈P₁⌉₊ ⌊P₂⌋₊).filter Nat.Prime,
          (p : ℂ)⁻¹ * Complex.exp (-(((t * Real.log p : ℝ) : ℂ) * I))‖ ≤
        CH * (1 / (|t| * Real.log Y) + 1 / Real.log Y ^ 5))
    (hCφ : ∀ ξ, ξ ^ 2 * ‖bumpHat ξ‖ ≤ Cφ)
    (hCθ : 0 ≤ Cθ)
    (hθH : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ Cθ * x / Real.log x ^ 10)
    (hθΘ : θs ε Y ≤ Θs Y) (hZ : 2 * π * (Real.log Y ^ 2 / θs ε Y) ≤ Y ^ 2)
    (hT : 6 * Real.log Y ^ 3 ≤ √Y)
    (hwin : (1 - ε / 8) * Y ≤ (Y - 1) * Real.exp (-(3 * Θs Y / 4)))
    (hθin : 2 ^ 11 * Cθ / Real.log Y ^ 10 ≤ Θs Y / 8)
    (hθout : 2 * 4 ^ 10 * Cθ / Real.log Y ^ 10 ≤ ε / 34)
    (hh : 1 ≤ ε * √Y / 16) :
    ((badBlock ε Y).card : ℝ) ≤
      2 * Y * (K₁ ε CMV CH Cφ / Real.log Y ^ 6) / (bumpMid * ε / (272 * Real.log Y ^ 2)) ^ 2 := by
  have hs4 := sqrtY_ge hε hε1 hY
  have hL2 := logY_ge_two hε hε1 hY
  have hθ := θs_pos hε hε1 hY
  have hΘ := Θs_pos hε hε1 hY
  have hbm := bumpMid_pos
  set Lb := bumpMid * ε / (272 * Real.log Y ^ 2) with hLb
  have hLb0 : 0 < Lb := by positivity
  set f : ℝ → ℝ := fun v =>
    ‖D (primesP ε Y ×ˢ primesK Y) cPK ℓPK (θs ε Y) (Θs Y) v‖ ^ 2 with hf
  have hint : Integrable f := integrable_norm_sq_D _ _ _ hθ hΘ
  have hf0 : ∀ v, 0 ≤ f v := fun v => by positivity
  have hms : ∫ v, f v ≤ K₁ ε CMV CH Cφ / Real.log Y ^ 6 :=
    meanSquare_le hε hε1 hY hCMV hMV hPS hCφ hθΘ hZ hT
  set E : Set ℝ := {v | Lb ^ 2 ≤ f v} with hE
  have hMarkov : Lb ^ 2 * volume.real E ≤ ∫ v, f v :=
    mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hint (Lb ^ 2)
  -- `E` has finite measure
  have hEsub : E ⊆ tsupport (D (primesP ε Y ×ˢ primesK Y) cPK ℓPK (θs ε Y) (Θs Y)) := by
    intro v hv
    apply subset_tsupport
    intro hD
    have : f v = 0 := by simp only [hf]; rw [hD]; simp
    have hv' : Lb ^ 2 ≤ f v := hv
    rw [this] at hv'
    have : 0 < Lb ^ 2 := by positivity
    linarith
  have hEfin : volume E ≠ ⊤ :=
    ((D_hasCompactSupport _ _ _ hθ hΘ).isCompact.measure_lt_top.trans_le'
      (measure_mono hEsub)).ne
  -- every exceptional `N` contributes an interval inside `E`
  have hblock : ∀ N ∈ badBlock ε Y, Set.Ico (Real.log ((N : ℝ) - 1)) (Real.log N) ⊆ E := by
    intro N hN v hv
    simp only [badBlock, mem_filter, mem_Icc] at hN
    obtain ⟨⟨hN1, hN2⟩, hbad⟩ := hN
    have hNY : Y ≤ N := Nat.ceil_le.mp hN1
    have hNY2 : (N : ℝ) ≤ (1 + ε / 8) * Y := (Nat.le_floor_iff (by positivity)).mp hN2
    have hN2' : 2 ≤ N := by
      have : (2 : ℝ) ≤ N := by linarith
      exact_mod_cast this
    have h2Y : (1 + ε / 8) * Y ≤ 2 * Y := by nlinarith
    have hvlo : Real.log (Y - 1) ≤ v :=
      (Real.log_le_log (by linarith) (by linarith)).trans hv.1
    have hvhi : v ≤ Real.log ((1 + ε / 8) * Y) :=
      hv.2.le.trans (Real.log_le_log (by linarith) hNY2)
    -- the short count vanishes
    have hFr0 : Fr (primesP ε Y) (primesK Y) (θs ε Y) v ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have hθN : θs ε Y * N ≤ ε * √Y / 8 - 1 := by
        have h1 : θs ε Y * N ≤ θs ε Y * (2 * Y) :=
          mul_le_mul_of_nonneg_left (by linarith) hθ.le
        have h2 : θs ε Y * (2 * Y) = ε * √Y / 16 := by
          unfold θs
          have hss := Real.mul_self_sqrt (show (0 : ℝ) ≤ Y by linarith)
          rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by norm_num)]
          linear_combination (-32 * ε) * hss
        linarith
      have hF := F_ge_of_Fr_pos hθ (fun p hp => ⟨(mem_primesP hε hε1 hY hp).1,
        (mem_primesP hε hε1 hY hp).2.1⟩) (fun k hk => (mem_primesK hε hε1 hY hk).1)
        (fun p hp k hk => p_le_k hε hε1 hY hp hk) hN2' hv.1 hv.2 hθN hpos
      have hsqN : √Y ≤ √(N : ℝ) := Real.sqrt_le_sqrt hNY
      have hsqN2 : √(N : ℝ) ≤ √((1 + ε / 8) * Y) := Real.sqrt_le_sqrt hNY2
      have hP₁N : (1 - ε / 4) * √(N : ℝ) ≤ P₁ ε Y :=
        mul_le_mul_of_nonneg_left hsqN2 (by linarith)
      have : (N : ℝ) + (1 - ε) * √(N : ℝ) ≤ N + (P₁ ε Y - ε * √Y / 8) := by
        nlinarith [Real.sqrt_nonneg (N : ℝ)]
      linarith
    have hFrθ : Fr (primesP ε Y) (primesK Y) (θs ε Y) v = 0 :=
      le_antisymm hFr0 (Fr_nonneg _ _ hθ v)
    have hFrΘ := Fr_long_ge hε hε1 hY hCθ hθH hwin hθin hθout hvlo hvhi
    show Lb ^ 2 ≤ f v
    simp only [hf]
    rw [show D (primesP ε Y ×ˢ primesK Y) cPK ℓPK (θs ε Y) (Θs Y) v =
        ((Fr (primesP ε Y) (primesK Y) (θs ε Y) v - Fr (primesP ε Y) (primesK Y) (Θs Y) v : ℝ) : ℂ)
        from D_eq_Fr _ _ _ _ v]
    rw [hFrθ, zero_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_sq]
    exact pow_le_pow_left₀ hLb0.le hFrΘ 2
  -- the intervals are disjoint
  have hdisj : Set.PairwiseDisjoint (↑(badBlock ε Y))
      (fun N : ℕ => Set.Ico (Real.log ((N : ℝ) - 1)) (Real.log N)) := by
    intro N hN N' hN' hne
    simp only [Finset.coe_filter, badBlock, Set.mem_ofPred_eq, mem_Icc] at hN hN'
    have hNpos : (2 : ℝ) ≤ N := by
      have := Nat.ceil_le.mp hN.1.1; linarith
    have hN'pos : (2 : ℝ) ≤ N' := by
      have := Nat.ceil_le.mp hN'.1.1; linarith
    rw [Function.onFun, Set.disjoint_left]
    intro v hv hv'
    rcases lt_or_gt_of_ne hne with h | h
    · have hle : (N : ℝ) ≤ (N' : ℝ) - 1 := by
        have : N + 1 ≤ N' := h
        have : ((N + 1 : ℕ) : ℝ) ≤ N' := by exact_mod_cast this
        push_cast at this; linarith
      have := Real.log_le_log (by linarith) hle
      linarith [hv.2, hv'.1]
    · have hle : (N' : ℝ) ≤ (N : ℝ) - 1 := by
        have : N' + 1 ≤ N := h
        have : ((N' + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
        push_cast at this; linarith
      have := Real.log_le_log (by linarith) hle
      linarith [hv'.2, hv.1]
  have hunion : volume.real (⋃ N ∈ badBlock ε Y, Set.Ico (Real.log ((N : ℝ) - 1)) (Real.log N)) =
      ∑ N ∈ badBlock ε Y, (Real.log N - Real.log ((N : ℝ) - 1)) := by
    rw [measureReal_biUnion_finset hdisj (fun N _ => measurableSet_Ico)
      (fun N _ => measure_Ico_lt_top.ne)]
    refine sum_congr rfl fun N hN => ?_
    simp only [badBlock, mem_filter, mem_Icc] at hN
    have : (2 : ℝ) ≤ N := by have := Nat.ceil_le.mp hN.1.1; linarith
    rw [Real.volume_real_Ico_of_le (Real.log_le_log (by linarith) (by linarith))]
  have hlen : ((badBlock ε Y).card : ℝ) / (2 * Y) ≤
      ∑ N ∈ badBlock ε Y, (Real.log N - Real.log ((N : ℝ) - 1)) := by
    rw [div_eq_mul_one_div, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun N hN => ?_
    simp only [badBlock, mem_filter, mem_Icc] at hN
    have h1 : Y ≤ N := Nat.ceil_le.mp hN.1.1
    have h2 : (N : ℝ) ≤ (1 + ε / 8) * Y := (Nat.le_floor_iff (by positivity)).mp hN.1.2
    have h2Y : (1 + ε / 8) * Y ≤ 2 * Y := by nlinarith
    have h3 : 1 / (2 * Y) ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le (by linarith) (by linarith)
    exact h3.trans (inv_le_log_sub_log (by linarith))
  have hmono : volume.real (⋃ N ∈ badBlock ε Y, Set.Ico (Real.log ((N : ℝ) - 1)) (Real.log N)) ≤
      volume.real E := measureReal_mono (Set.iUnion₂_subset hblock) hEfin
  have hYpos : 0 < 2 * Y := by linarith
  have hcount : ((badBlock ε Y).card : ℝ) / (2 * Y) ≤ (K₁ ε CMV CH Cφ / Real.log Y ^ 6) / Lb ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc ((badBlock ε Y).card : ℝ) / (2 * Y) * Lb ^ 2 ≤ volume.real E * Lb ^ 2 :=
          mul_le_mul_of_nonneg_right ((hlen.trans hunion.symm.le).trans hmono) (by positivity)
      _ = Lb ^ 2 * volume.real E := mul_comm _ _
      _ ≤ ∫ v, f v := hMarkov
      _ ≤ K₁ ε CMV CH Cφ / Real.log Y ^ 6 := hms
  rw [div_le_iff₀ hYpos] at hcount
  calc ((badBlock ε Y).card : ℝ) ≤ (K₁ ε CMV CH Cφ / Real.log Y ^ 6) / Lb ^ 2 * (2 * Y) := hcount
    _ = 2 * Y * (K₁ ε CMV CH Cφ / Real.log Y ^ 6) / Lb ^ 2 := by ring

end Block

end Erdos430Sqrt
