import Erdos430Sqrt.Fourier
import Erdos430Sqrt.Hypotheses

/-!
# Smoothed counts of products `p k`, and the long-average lower bound

`Fr Ps Ks ϑ v = ∑_{p ∈ Ps, k ∈ Ks} (p k)⁻¹ ϑ⁻¹ bump ((v - log p - log k) / ϑ)` is the smoothed
count at scale `ϑ`. This file relates it to `D`, extracts a witness `p k` from a positive
value, and bounds it from below by counting primes in short intervals with Chebyshev's `θ`.
-/

open MeasureTheory Complex Real Finset
open scoped Chebyshev

noncomputable section

namespace Erdos430Sqrt

/-- The smoothed count at scale `ϑ`. -/
def Fr (Ps Ks : Finset ℕ) (ϑ v : ℝ) : ℝ :=
  ∑ x ∈ Ps ×ˢ Ks, 1 / ((x.1 : ℝ) * x.2) *
    (ϑ⁻¹ * bump ((v - (Real.log x.1 + Real.log x.2)) / ϑ))

theorem Fr_nonneg (Ps Ks : Finset ℕ) {ϑ : ℝ} (hϑ : 0 < ϑ) (v : ℝ) : 0 ≤ Fr Ps Ks ϑ v :=
  sum_nonneg fun x _ => mul_nonneg (by positivity)
    (mul_nonneg (inv_nonneg.mpr hϑ.le) (bump_nonneg _))

theorem D_eq_Fr (Ps Ks : Finset ℕ) (ϑ₁ ϑ₂ v : ℝ) :
    D (Ps ×ˢ Ks) (fun x => 1 / ((x.1 : ℝ) * x.2)) (fun x => Real.log x.1 + Real.log x.2) ϑ₁ ϑ₂ v =
      ((Fr Ps Ks ϑ₁ v - Fr Ps Ks ϑ₂ v : ℝ) : ℂ) := by
  unfold D Fr bumpAt
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  ring

/-- A positive smoothed count at scale `ϑ` produces a product `p k` with
`v - ϑ < log p + log k < v`. -/
theorem exists_of_Fr_pos {Ps Ks : Finset ℕ} {ϑ v : ℝ} (hϑ : 0 < ϑ) (h : 0 < Fr Ps Ks ϑ v) :
    ∃ x ∈ Ps ×ˢ Ks, v - ϑ < Real.log x.1 + Real.log x.2 ∧ Real.log x.1 + Real.log x.2 < v := by
  by_contra hne
  push Not at hne
  have : Fr Ps Ks ϑ v = 0 := by
    apply sum_eq_zero
    intro x hx
    have hb : bump ((v - (Real.log x.1 + Real.log x.2)) / ϑ) = 0 := by
      apply bump_eq_zero_of_not_mem
      by_cases h1 : v - ϑ < Real.log x.1 + Real.log x.2
      · left
        have := hne x hx h1
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hϑ.le
      · right
        rw [le_div_iff₀ hϑ]
        linarith
    rw [hb, mul_zero, mul_zero]
  linarith

/-! ### Counting primes with `θ` -/

/-- `θ(B) - θ(A)` is the sum of `log p` over primes in `(⌊A⌋, ⌊B⌋]`. -/
theorem theta_sub_eq (A B : ℝ) (hAB : ⌊A⌋₊ ≤ ⌊B⌋₊) :
    θ B - θ A = ∑ p ∈ (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  have hsub : (Icc 0 ⌊A⌋₊).filter Nat.Prime ⊆ (Icc 0 ⌊B⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hAB⟩, hp.2⟩
  rw [← sum_sdiff hsub, add_sub_cancel_right]
  congr 1
  ext p
  simp only [mem_sdiff, mem_filter, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨⟨_, h2⟩, hp⟩, h3⟩
    refine ⟨⟨?_, h2⟩, hp⟩
    by_contra h
    exact h3 ⟨⟨Nat.zero_le _, by omega⟩, hp⟩
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨⟨Nat.zero_le _, h2⟩, hp⟩, fun h => by omega⟩

/-- The number of primes in `(⌊A⌋, ⌊B⌋]` is at least `(θ(B) - θ(A)) / log B`. -/
theorem theta_sub_le_card_mul_log {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    θ B - θ A ≤ ((Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime).card * Real.log B := by
  rw [theta_sub_eq A B (Nat.floor_le_floor hAB)]
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun p hp => ?_
  simp only [mem_filter, mem_Ioc] at hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
  have hpB : (p : ℝ) ≤ B := (Nat.cast_le.mpr hp.1.2).trans (Nat.floor_le (hA.trans hAB))
  exact Real.log_le_log hp0 hpB

/-- With the `θ` hypothesis, a lower bound for `θ(B) - θ(A)`. -/
theorem theta_sub_ge {C : ℝ} (hC0 : 0 ≤ C)
    (hθ : ∀ x : ℝ, 2 ≤ x → |θ x - x| ≤ C * x / Real.log x ^ 10)
    {A B : ℝ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    (B - A) - 2 * C * B / Real.log A ^ 10 ≤ θ B - θ A := by
  have hB := hθ B (hA.trans hAB)
  have hA' := hθ A hA
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  have hlogAB : Real.log A ≤ Real.log B := Real.log_le_log (by linarith) hAB
  have h1 : C * B / Real.log B ^ 10 ≤ C * B / Real.log A ^ 10 := by
    apply div_le_div_of_nonneg_left (mul_nonneg hC0 (by linarith)) (by positivity)
    exact pow_le_pow_left₀ hlogA.le hlogAB 10
  have h2 : C * A / Real.log A ^ 10 ≤ C * B / Real.log A ^ 10 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hAB hC0
  have := abs_le.mp hB
  have := abs_le.mp hA'
  rw [show 2 * C * B / Real.log A ^ 10 = C * B / Real.log A ^ 10 + C * B / Real.log A ^ 10 by
    ring]
  linarith

/-! ### The long-average lower bound -/

/-- For one prime `p`: the inner smoothed count is at least `bumpMid / (8 L)`, provided the
primes in the window `(⌊A⌋, ⌊B⌋]` lie in `Ks`, `θ(B) - θ(A) ≥ Θ B / 8` and `log B ≤ L`, where
`A = exp(v - 3Θ/4)/p` and `B = exp(v - Θ/4)/p`. -/
theorem inner_ge {Ks : Finset ℕ} {p : ℕ} (hp : 0 < p) {Θ v L : ℝ} (hΘ : 0 < Θ)
    (hsub : ((Ioc ⌊Real.exp (v - 3 * Θ / 4) / p⌋₊ ⌊Real.exp (v - Θ / 4) / p⌋₊).filter Nat.Prime) ⊆ Ks)
    (hθ : Θ * (Real.exp (v - Θ / 4) / p) / 8 ≤
      θ (Real.exp (v - Θ / 4) / p) - θ (Real.exp (v - 3 * Θ / 4) / p))
    (hB1 : 1 < Real.exp (v - Θ / 4) / p) (hL : Real.log (Real.exp (v - Θ / 4) / p) ≤ L) :
    bumpMid / (8 * L) * (1 / (p : ℝ)) ≤
      ∑ k ∈ Ks, 1 / ((p : ℝ) * k) * (Θ⁻¹ * bump ((v - (Real.log p + Real.log k)) / Θ)) := by
  set A := Real.exp (v - 3 * Θ / 4) / p with hAdef
  set B := Real.exp (v - Θ / 4) / p with hBdef
  set W := (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime with hW
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hA0 : 0 < A := by positivity
  have hAB : A ≤ B := by
    apply div_le_div_of_nonneg_right _ hp'.le
    exact Real.exp_le_exp.mpr (by linarith)
  have hlogB : 0 < Real.log B := Real.log_pos hB1
  have hLpos : 0 < L := hlogB.trans_le hL
  -- each term in the window is at least `(p B)⁻¹ Θ⁻¹ bumpMid`
  have hterm : ∀ k ∈ W, 1 / ((p : ℝ) * B) * (Θ⁻¹ * bumpMid) ≤
      1 / ((p : ℝ) * k) * (Θ⁻¹ * bump ((v - (Real.log p + Real.log k)) / Θ)) := by
    intro k hk
    simp only [hW, mem_filter, mem_Ioc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.2.pos
    have hkA : A < k := by
      have := Nat.lt_floor_add_one A
      have h2 : ((⌊A⌋₊ : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hk.1.1
      linarith
    have hkB : (k : ℝ) ≤ B := (Nat.cast_le.mpr hk.1.2).trans (Nat.floor_le (hA0.le.trans hAB))
    have hlogk1 : Real.log A < Real.log k := Real.log_lt_log hA0 hkA
    have hlogk2 : Real.log k ≤ Real.log B := Real.log_le_log hk0 hkB
    have hlA : Real.log A = v - 3 * Θ / 4 - Real.log p := by
      rw [hAdef, Real.log_div (Real.exp_pos _).ne' hp'.ne', Real.log_exp]
    have hlB : Real.log B = v - Θ / 4 - Real.log p := by
      rw [hBdef, Real.log_div (Real.exp_pos _).ne' hp'.ne', Real.log_exp]
    have hmid : bump ((v - (Real.log p + Real.log k)) / Θ) = bumpMid := by
      apply bump_mid
      constructor
      · rw [le_div_iff₀ hΘ]; linarith
      · rw [div_le_iff₀ hΘ]; linarith
    rw [hmid]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr hΘ.le) bumpMid_pos.le)
    apply one_div_le_one_div_of_le (mul_pos hp' hk0)
    exact mul_le_mul_of_nonneg_left hkB hp'.le
  have hcard : Θ * B / 8 / Real.log B ≤ W.card := by
    rw [div_le_iff₀ hlogB]
    exact hθ.trans (theta_sub_le_card_mul_log hA0.le hAB)
  calc bumpMid / (8 * L) * (1 / (p : ℝ))
      ≤ bumpMid / (8 * Real.log B) * (1 / (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_left bumpMid_pos.le (by positivity)
        linarith
    _ = Θ * B / 8 / Real.log B * (1 / ((p : ℝ) * B) * (Θ⁻¹ * bumpMid)) := by
        field_simp
    _ ≤ W.card * (1 / ((p : ℝ) * B) * (Θ⁻¹ * bumpMid)) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (one_div_nonneg.mpr (mul_pos hp'
          (hA0.trans_le hAB)).le) (mul_nonneg (inv_nonneg.mpr hΘ.le) bumpMid_pos.le))
    _ = ∑ _k ∈ W, 1 / ((p : ℝ) * B) * (Θ⁻¹ * bumpMid) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ W, 1 / ((p : ℝ) * k) * (Θ⁻¹ * bump ((v - (Real.log p + Real.log k)) / Θ)) :=
        sum_le_sum hterm
    _ ≤ ∑ k ∈ Ks, 1 / ((p : ℝ) * k) * (Θ⁻¹ * bump ((v - (Real.log p + Real.log k)) / Θ)) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro k _ _
        exact mul_nonneg (by positivity) (mul_nonneg (inv_nonneg.mpr hΘ.le) (bump_nonneg _))

/-- The long-average lower bound, summed over `p`. -/
theorem Fr_ge {Ps Ks : Finset ℕ} {Θ v L : ℝ}
    (hinner : ∀ p ∈ Ps, bumpMid / (8 * L) * (1 / (p : ℝ)) ≤
      ∑ k ∈ Ks, 1 / ((p : ℝ) * k) * (Θ⁻¹ * bump ((v - (Real.log p + Real.log k)) / Θ))) :
    bumpMid / (8 * L) * ∑ p ∈ Ps, (1 / (p : ℝ)) ≤ Fr Ps Ks Θ v := by
  rw [Fr, sum_product, mul_sum]
  exact sum_le_sum hinner

/-- A lower bound for `∑_{p ∈ Ps} 1/p` when `Ps` contains the primes in `(⌊P₁⌋, ⌊P₂⌋]`. -/
theorem sum_inv_primes_ge {Ps : Finset ℕ} {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂)
    (hP₂ : 0 < P₂) (hsub : (Ioc ⌊P₁⌋₊ ⌊P₂⌋₊).filter Nat.Prime ⊆ Ps)
    (hlog : 0 < Real.log P₂) :
    (θ P₂ - θ P₁) / (P₂ * Real.log P₂) ≤ ∑ p ∈ Ps, (1 / (p : ℝ)) := by
  set W := (Ioc ⌊P₁⌋₊ ⌊P₂⌋₊).filter Nat.Prime with hW
  have hcard := theta_sub_le_card_mul_log hP₁ hP
  have hWle : ∀ p ∈ W, 1 / P₂ ≤ 1 / (p : ℝ) := by
    intro p hp
    simp only [hW, mem_filter, mem_Ioc] at hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    exact one_div_le_one_div_of_le hp0
      ((Nat.cast_le.mpr hp.1.2).trans (Nat.floor_le (hP₁.trans hP)))
  calc (θ P₂ - θ P₁) / (P₂ * Real.log P₂) ≤ W.card * Real.log P₂ / (P₂ * Real.log P₂) :=
        div_le_div_of_nonneg_right hcard (by positivity)
    _ = ∑ _p ∈ W, 1 / P₂ := by rw [sum_const, nsmul_eq_mul]; field_simp
    _ ≤ ∑ p ∈ W, (1 / (p : ℝ)) := sum_le_sum hWle
    _ ≤ ∑ p ∈ Ps, (1 / (p : ℝ)) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro p _ _
        positivity

end Erdos430Sqrt
