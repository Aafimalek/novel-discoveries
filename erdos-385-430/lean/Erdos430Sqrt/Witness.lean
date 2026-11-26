import Erdos430
import Erdos430Sqrt.Counts

/-!
# From a positive smoothed count to a large value of `F`

If the smoothed count at scale `θ` is positive at `log x` with `N - 1 ≤ x < N`, then some
product `m = p k` of primes `p ≤ k` lies in `[N - h, N)`, and `F N ≥ m + p`.
-/

open Real Finset

noncomputable section

namespace Erdos430Sqrt

/-- The least prime factor of `p k` is `p` for primes `p ≤ k`. -/
theorem minFac_mul_primes {p k : ℕ} (hp : p.Prime) (hk : k.Prime) (hpk : p ≤ k) :
    (p * k).minFac = p := by
  apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p k))
  have hq := Nat.minFac_prime (show p * k ≠ 1 by
    intro h; exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h))
  rcases (Nat.Prime.dvd_mul hq).mp (Nat.minFac_dvd (p * k)) with h | h
  · exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).ge
  · exact hpk.trans ((Nat.prime_dvd_prime_iff_eq hq hk).mp h).ge

/-- **The witness step.** If the smoothed count at scale `θ` is positive at some point of
`[log (N - 1), log N)`, then `F N ≥ N + (P₁ - h)`, where every `p ∈ Ps` is at least `P₁`, every
`k ∈ Ks` is at least every `p`, and `θ N ≤ h - 1`. -/
theorem F_ge_of_Fr_pos {Ps Ks : Finset ℕ} {N : ℕ} {θ h P₁ v : ℝ} (hθ : 0 < θ)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ P₁ ≤ p) (hKs : ∀ k ∈ Ks, k.Prime)
    (hpk : ∀ p ∈ Ps, ∀ k ∈ Ks, p ≤ k) (hN : 2 ≤ N)
    (hv1 : Real.log (N - 1) ≤ v) (hv2 : v < Real.log N) (hθN : θ * N ≤ h - 1)
    (hpos : 0 < Fr Ps Ks θ v) :
    (N : ℝ) + (P₁ - h) ≤ Erdos430.F N := by
  obtain ⟨⟨p, k⟩, hx, hlo, hhi⟩ := exists_of_Fr_pos hθ hpos
  rw [mem_product] at hx
  obtain ⟨hpP, hkK⟩ := hx
  obtain ⟨hpprime, hP₁p⟩ := hPs p hpP
  have hkprime := hKs k hkK
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hkprime.pos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlogm : Real.log ((p * k : ℕ) : ℝ) = Real.log p + Real.log k := by
    push_cast; exact Real.log_mul hp0.ne' hk0.ne'
  set m := p * k with hm
  have hm0 : (0 : ℝ) < m := by rw [hm]; push_cast; positivity
  -- `m < N`
  have hmx : (m : ℝ) < Real.exp v := by
    rw [← Real.exp_log hm0, hlogm]; exact Real.exp_lt_exp.mpr hhi
  have hxN : Real.exp v < N := by
    rw [← Real.exp_log (show (0 : ℝ) < N by linarith)]; exact Real.exp_lt_exp.mpr hv2
  have hmN : m < N := by exact_mod_cast hmx.trans hxN
  -- `m ≥ N - h`
  have hxlo : (N : ℝ) - 1 ≤ Real.exp v := by
    rw [← Real.exp_log (show (0 : ℝ) < N - 1 by linarith)]; exact Real.exp_le_exp.mpr hv1
  have hmlo : Real.exp v * Real.exp (-θ) < m := by
    rw [← Real.exp_add, ← Real.exp_log hm0, hlogm]; exact Real.exp_lt_exp.mpr (by linarith)
  have hexp : 1 - θ ≤ Real.exp (-θ) := by linarith [Real.add_one_le_exp (-θ)]
  have hmh : (N : ℝ) - h ≤ m := by
    have h1 : Real.exp v * (1 - θ) ≤ Real.exp v * Real.exp (-θ) :=
      mul_le_mul_of_nonneg_left hexp (Real.exp_pos v).le
    have h2 : Real.exp v * θ ≤ N * θ := mul_le_mul_of_nonneg_right hxN.le hθ.le
    nlinarith
  -- `F N ≥ m + p`
  have hm1 : 1 < m := by
    rw [hm]; exact Nat.one_lt_mul_iff.mpr ⟨hpprime.pos, hkprime.pos, Or.inl hpprime.one_lt⟩
  have hmnp : ¬ m.Prime := Nat.not_prime_mul hpprime.one_lt.ne' hkprime.one_lt.ne'
  have hminFac : m.minFac = p := minFac_mul_primes hpprime hkprime (hpk p hpP k hkK)
  have hval : m + m.minFac ∈ Erdos430.values N := ⟨m, hmN, hm1, hmnp, rfl⟩
  have hF := Erdos430.le_F hval
  rw [hminFac] at hF
  have hF' : ((m + p : ℕ) : ℝ) ≤ Erdos430.F N := by exact_mod_cast hF
  push_cast at hF'
  linarith

end Erdos430Sqrt
