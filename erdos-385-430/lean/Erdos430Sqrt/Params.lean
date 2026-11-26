import Erdos430Sqrt.MeanSquare
import Erdos430Sqrt.Poly
import Erdos430Sqrt.Witness

/-!
# Parameters of the proof and their elementary properties

For `0 < ε ≤ 1` and `Y ≥ 16` we fix
`P₁ = (1 - ε/4) √((1 + ε/8) Y)`, `P₂ = (1 - ε/8) √Y`, the primes `p ∈ [P₁, P₂]`, the primes
`k ∈ [√Y, 3√Y]`, `θ = ε / (32 √Y)`, `Θ = (log Y)⁻⁶` and `h = ε √Y / 8`.
-/

open MeasureTheory Complex Real Finset

noncomputable section

namespace Erdos430Sqrt

/-- `P₁ = (1 - ε/4) √((1 + ε/8) Y)`. -/
def P₁ (ε Y : ℝ) : ℝ := (1 - ε / 4) * √((1 + ε / 8) * Y)

/-- `P₂ = (1 - ε/8) √Y`. -/
def P₂ (ε Y : ℝ) : ℝ := (1 - ε / 8) * √Y

/-- The primes in `[P₁, P₂]`. -/
def primesP (ε Y : ℝ) : Finset ℕ := (Icc ⌈P₁ ε Y⌉₊ ⌊P₂ ε Y⌋₊).filter Nat.Prime

/-- The primes in `[√Y, 3√Y]`. -/
def primesK (Y : ℝ) : Finset ℕ := (Icc ⌈√Y⌉₊ ⌊3 * √Y⌋₊).filter Nat.Prime

/-- The short scale `θ = ε / (32 √Y)`. -/
def θs (ε Y : ℝ) : ℝ := ε / (32 * √Y)

/-- The long scale `Θ = (log Y)⁻⁶`. -/
def Θs (Y : ℝ) : ℝ := 1 / Real.log Y ^ 6

section Facts

variable {ε Y : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hY : 16 ≤ Y)
include hε hε1 hY

theorem sqrtY_ge : 4 ≤ √Y := by
  rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt hY

theorem logY_ge : 1 ≤ Real.log Y := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem sqrt_mul_le : √((1 + ε / 8) * Y) ≤ (1 + ε / 16) * √Y := by
  rw [Real.sqrt_mul (by linarith), mul_le_mul_iff_of_pos_right (by linarith [sqrtY_ge hε hε1 hY])]
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · nlinarith

theorem sqrt_mul_ge : √Y ≤ √((1 + ε / 8) * Y) :=
  Real.sqrt_le_sqrt (by nlinarith)

theorem P₁_ge : 3 / 4 * √Y ≤ P₁ ε Y := by
  have := sqrt_mul_ge hε hε1 hY
  have h4 := sqrtY_ge hε hε1 hY
  unfold P₁
  nlinarith

theorem P₁_mul_le_P₂ : P₁ ε Y * (1 + ε / 16) ≤ P₂ ε Y := by
  have hs := sqrt_mul_le hε hε1 hY
  have h4 := sqrtY_ge hε hε1 hY
  unfold P₁ P₂
  have h1 : (1 - ε / 4) * √((1 + ε / 8) * Y) ≤ (1 - ε / 4) * ((1 + ε / 16) * √Y) :=
    mul_le_mul_of_nonneg_left hs (by linarith)
  have h2 : (1 - ε / 4) * ((1 + ε / 16) * √Y) * (1 + ε / 16) ≤ (1 - ε / 8) * √Y := by
    have : (1 - ε / 4) * (1 + ε / 16) * (1 + ε / 16) ≤ 1 - ε / 8 := by
      have hexp : (1 - ε / 4) * (1 + ε / 16) * (1 + ε / 16) =
          1 - ε / 8 - 7 * ε ^ 2 / 256 - ε ^ 3 / 1024 := by ring
      rw [hexp]
      nlinarith [pow_pos hε 2, pow_pos hε 3]
    nlinarith
  nlinarith

theorem P₂_le : P₂ ε Y ≤ √Y := by
  unfold P₂; nlinarith [sqrtY_ge hε hε1 hY]

theorem P₁_le_P₂ : P₁ ε Y ≤ P₂ ε Y := by
  have h := P₁_mul_le_P₂ hε hε1 hY
  have h0 := P₁_ge hε hε1 hY
  have h4 := sqrtY_ge hε hε1 hY
  nlinarith

theorem mem_primesP {p : ℕ} (hp : p ∈ primesP ε Y) : p.Prime ∧ P₁ ε Y ≤ p ∧ (p : ℝ) ≤ P₂ ε Y := by
  simp only [primesP, mem_filter, mem_Icc] at hp
  have hP₂ : 0 ≤ P₂ ε Y := (P₁_ge hε hε1 hY).trans' (by positivity) |>.trans (P₁_le_P₂ hε hε1 hY)
  exact ⟨hp.2, Nat.ceil_le.mp hp.1.1, (Nat.le_floor_iff hP₂).mp hp.1.2⟩

theorem mem_primesK {k : ℕ} (hk : k ∈ primesK Y) : k.Prime ∧ √Y ≤ k ∧ (k : ℝ) ≤ 3 * √Y := by
  simp only [primesK, mem_filter, mem_Icc] at hk
  exact ⟨hk.2, Nat.ceil_le.mp hk.1.1, (Nat.le_floor_iff (by positivity)).mp hk.1.2⟩

theorem p_le_k {p k : ℕ} (hp : p ∈ primesP ε Y) (hk : k ∈ primesK Y) : p ≤ k := by
  have h1 := (mem_primesP hε hε1 hY hp).2.2
  have h2 := (mem_primesK hε hε1 hY hk).2.1
  have := P₂_le hε hε1 hY
  exact_mod_cast (h1.trans this).trans h2

/-- `∑_{p} 1/p ≤ 2`. -/
theorem sum_inv_primesP_le : ∑ p ∈ primesP ε Y, (1 / (p : ℝ)) ≤ 2 := by
  have hP₁ := P₁_ge hε hε1 hY
  have h4 := sqrtY_ge hε hε1 hY
  have hpos : 0 < P₁ ε Y := by linarith
  refine (sum_inv_le_card_div hpos fun p hp => (mem_primesP hε hε1 hY hp).2.1).trans ?_
  have hcard : ((primesP ε Y).card : ℝ) ≤ P₂ ε Y + 1 := by
    have h1 : (primesP ε Y).card ≤ ⌊P₂ ε Y⌋₊ + 1 := by
      refine (card_filter_le _ _).trans ?_
      rw [Nat.card_Icc]; omega
    have h2 : ((⌊P₂ ε Y⌋₊ : ℕ) : ℝ) ≤ P₂ ε Y :=
      Nat.floor_le (hpos.le.trans (P₁_le_P₂ hε hε1 hY))
    have h3 : ((primesP ε Y).card : ℝ) ≤ ((⌊P₂ ε Y⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  rw [div_le_iff₀ hpos]
  have := P₂_le hε hε1 hY
  linarith

/-- `∑_{k} 1/k² ≤ 4 / √Y`. -/
theorem sum_inv_sq_primesK_le : ∑ k ∈ primesK Y, (1 / (k : ℝ)) ^ 2 ≤ 4 / √Y := by
  have h4 := sqrtY_ge hε hε1 hY
  have hpos : 0 < √Y := by linarith
  refine (sum_inv_sq_le_card_div hpos fun k hk => (mem_primesK hε hε1 hY hk).2.1).trans ?_
  have hcard : ((primesK Y).card : ℝ) ≤ 3 * √Y + 1 := by
    have h1 : (primesK Y).card ≤ ⌊3 * √Y⌋₊ + 1 := by
      refine (card_filter_le _ _).trans ?_
      rw [Nat.card_Icc]; omega
    have h2 : ((⌊3 * √Y⌋₊ : ℕ) : ℝ) ≤ 3 * √Y := Nat.floor_le (by positivity)
    have h3 : ((primesK Y).card : ℝ) ≤ ((⌊3 * √Y⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  rw [Real.sq_sqrt (by linarith), div_le_div_iff₀ (by linarith) hpos]
  have hYs : Y = √Y * √Y := (Real.mul_self_sqrt (by linarith)).symm
  nlinarith

theorem primesK_subset : primesK Y ⊆ Icc 1 ⌊3 * √Y⌋₊ := by
  intro k hk
  have hk' := mem_primesK hε hε1 hY hk
  simp only [primesK, mem_filter, mem_Icc] at hk
  exact mem_Icc.mpr ⟨hk'.1.one_lt.le, hk.1.2⟩

/-- The mean value bound for the cofactor polynomial: `∫_{-R}^{R} ‖K‖² ≤ (8/√Y) R + 2C`. -/
theorem mvt_primesK {C : ℝ} (hC : 0 ≤ C)
    (hMV : ∀ (N : ℕ) (b : ℕ → ℂ) (T : ℝ), 0 ≤ T →
      ∫ t in -T..T, mvSum N b t ≤ (2 * T + C * N) * ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∫ w in -R..R, ‖polyW (primesK Y) w‖ ^ 2 ≤ 8 / √Y * R + 2 * C := by
  have h4 := sqrtY_ge hε hε1 hY
  have hpos : 0 < √Y := by linarith
  refine (mvt_polyW hMV (primesK_subset hε hε1 hY) hR).trans ?_
  have hS := sum_inv_sq_primesK_le hε hε1 hY
  have hN : ((⌊3 * √Y⌋₊ : ℕ) : ℝ) ≤ 3 * √Y := Nat.floor_le (by positivity)
  have hS0 : 0 ≤ ∑ k ∈ primesK Y, (1 / (k : ℝ)) ^ 2 := sum_nonneg fun _ _ => by positivity
  have hfac : 0 ≤ 2 * R + C * ⌊3 * √Y⌋₊ / (2 * π) := by positivity
  calc (2 * R + C * ⌊3 * √Y⌋₊ / (2 * π)) * ∑ k ∈ primesK Y, (1 / (k : ℝ)) ^ 2
      ≤ (2 * R + C * (3 * √Y) / (2 * π)) * (4 / √Y) := by
        apply mul_le_mul _ hS hS0 (by positivity)
        gcongr
    _ = 8 / √Y * R + 6 * C / π := by field_simp; ring
    _ ≤ 8 / √Y * R + 2 * C := by
        have hπ : 3 ≤ π := Real.pi_gt_three.le
        have : 6 * C / π ≤ 2 * C := by
          rw [div_le_iff₀ Real.pi_pos]; nlinarith
        linarith

/-- The prime polynomial in the hypothesis form equals `polyW`. -/
theorem polyW_primesP_eq (w : ℝ) :
    polyW (primesP ε Y) w = ∑ p ∈ (Icc ⌈P₁ ε Y⌉₊ ⌊P₂ ε Y⌋₊).filter Nat.Prime,
      (p : ℂ)⁻¹ * Complex.exp (-((((2 * π * w) * Real.log p : ℝ) : ℂ) * I)) := by
  unfold polyW primesP
  refine sum_congr rfl fun p _ => ?_
  congr 2
  push_cast
  ring

end Facts

end Erdos430Sqrt
