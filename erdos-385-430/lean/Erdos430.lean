import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic

/-!
# Erdős Problems 385 and 430: the elementary reductions

`F n` is the largest value of `m + p(m)` over composite `m < n`, where `p(m)` is the least
prime factor (Erdős Problem 385). `terms n` is the set from Erdős Problem 430: the integers
`1 < m < n` all of whose prime factors exceed `n - m`.

The file proves:

* `forall_terms_prime_iff`: every term is prime exactly when `F n ≤ n`, so Problem 430 is
  part (i) of Problem 385 (`erdos430_iff_erdos385_i`).
* `lt_F_iff`: `n < F n` exactly when some prime `p` with `p ∤ n` and `p * p < n` has
  `p ≤ minFac (n / p)`. The witness `m` is `p * (n / p)`, the multiple of `p` just below `n`.
* `lt_F_of_odd`, `le_F_of_even`, `lt_F_of_not_prime_pred`: every exception `n ≥ 7` is even,
  has `n - 1` prime, and has `F n = n`.
-/

namespace Erdos430

/-- The terms of the sequence in Erdős Problem 430. -/
def terms (n : ℕ) : Finset ℕ :=
  (Finset.Ioo 1 n).filter fun m => ∀ p ∈ m.primeFactors, n - m < p

/-- The values `m + p(m)` over composite `m < n`. -/
def values (n : ℕ) : Set ℕ :=
  {x | ∃ m, m < n ∧ 1 < m ∧ ¬ m.Prime ∧ x = m + m.minFac}

/-- `F n = max {m + p(m) : m < n composite}` from Erdős Problem 385 (`0` if there is none). -/
noncomputable def F (n : ℕ) : ℕ := sSup (values n)

theorem values_bddAbove (n : ℕ) : BddAbove (values n) := by
  refine ⟨2 * n, ?_⟩
  rintro x ⟨m, hmn, hm1, -, rfl⟩
  have : m.minFac ≤ m := Nat.minFac_le (by omega)
  omega

theorem le_F {n x : ℕ} (hx : x ∈ values n) : x ≤ F n :=
  le_csSup (values_bddAbove n) hx

theorem F_le_iff {n a : ℕ} : F n ≤ a ↔ ∀ x ∈ values n, x ≤ a :=
  ⟨fun h _ hx => (le_F hx).trans h, fun h => csSup_le' h⟩

/-- A composite `m < n` with `n < m + p(m)` is a term of Problem 430. -/
theorem mem_terms_of_lt {n m : ℕ} (hmn : m < n) (hm1 : 1 < m)
    (h : n < m + m.minFac) : m ∈ terms n := by
  simp only [terms, Finset.mem_filter, Finset.mem_Ioo]
  refine ⟨⟨hm1, hmn⟩, fun p hp => ?_⟩
  have hpm : m.minFac ≤ p :=
    Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
      (Nat.dvd_of_mem_primeFactors hp)
  omega

/-- **Problem 430 is part (i) of Problem 385.** Every term is prime exactly when
`F n ≤ n`. -/
theorem forall_terms_prime_iff (n : ℕ) : (∀ m ∈ terms n, m.Prime) ↔ F n ≤ n := by
  constructor
  · intro h
    rw [F_le_iff]
    rintro x ⟨m, hmn, hm1, hmp, rfl⟩
    by_contra hlt
    exact hmp (h m (mem_terms_of_lt hmn hm1 (by omega)))
  · intro h m hm
    simp only [terms, Finset.mem_filter, Finset.mem_Ioo] at hm
    obtain ⟨⟨hm1, hmn⟩, hfac⟩ := hm
    by_contra hmp
    have hmin : m.minFac ∈ m.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, by omega⟩
    have hval : m + m.minFac ∈ values n := ⟨m, hmn, hm1, hmp, rfl⟩
    have := hfac _ hmin
    have := le_F hval
    omega

/-- **Problem 430 is equivalent to part (i) of Problem 385**, stated with eventually
quantifiers as in the Formal Conjectures repository. -/
theorem erdos430_iff_erdos385_i :
    (∀ᶠ n in Filter.atTop, ¬ ∀ m ∈ terms n, m.Prime) ↔ (∀ᶠ n in Filter.atTop, n < F n) := by
  simp only [forall_terms_prime_iff, not_le]

/-- The multiple of `p` just below `n` gives a value above `n`. -/
theorem lt_F_of_witness {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hpp : p * p < n)
    (hmin : p ≤ (n / p).minFac) : n < F n := by
  have hp2 := hp.two_le
  have hk : p ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr hpp.le
  set k := n / p with hkdef
  have hk1 : k ≠ 1 := by omega
  have hminfac : (p * k).minFac = p := by
    apply le_antisymm (Nat.minFac_le_of_dvd hp2 (dvd_mul_right p k))
    have hq := Nat.minFac_prime (show p * k ≠ 1 by
      intro h; exact absurd (Nat.eq_one_of_mul_eq_one_right h) (by omega))
    rcases (Nat.Prime.dvd_mul hq).mp (Nat.minFac_dvd (p * k)) with h | h
    · exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).ge
    · exact hmin.trans (Nat.minFac_le_of_dvd hq.two_le h)
  have hlt : p * k < n := by
    have hle : p * k ≤ n := Nat.mul_div_le n p
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd ⟨k, h.symm⟩ hpn
  have hval : p * k + p ∈ values n := by
    refine ⟨p * k, hlt, by nlinarith, Nat.not_prime_mul (by omega) hk1, ?_⟩
    rw [hminfac]
  have hsucc : n < p * (k + 1) := Nat.lt_mul_div_succ n hp.pos
  have := le_F hval
  nlinarith

/-- **Criterion.** `n < F n` exactly when some prime `p` with `p ∤ n` and `p * p < n` has
`n / p` free of prime factors below `p`. -/
theorem lt_F_iff (n : ℕ) :
    n < F n ↔ ∃ p, p.Prime ∧ ¬ p ∣ n ∧ p * p < n ∧ p ≤ (n / p).minFac := by
  constructor
  · intro h
    have : ∃ x ∈ values n, n < x := by
      by_contra hne
      push Not at hne
      exact absurd (F_le_iff.mpr hne) (by omega)
    obtain ⟨x, ⟨m, hmn, hm1, hmp, rfl⟩, hx⟩ := this
    set p := m.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hp2 := hp.two_le
    obtain ⟨k, hk⟩ : p ∣ m := Nat.minFac_dvd m
    have hsq : p ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hmp
    have hpk : p ≤ k := by nlinarith
    have hdiv : n / p = k := by
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    refine ⟨p, hp, ?_, by nlinarith, ?_⟩
    · rintro ⟨j, hj⟩
      have hjk : j = k := by rw [← hdiv, hj, Nat.mul_div_cancel_left j hp.pos]
      subst hjk
      omega
    · rw [hdiv]
      have hk1 : k ≠ 1 := by omega
      exact Nat.minFac_le_of_dvd (Nat.minFac_prime hk1).two_le
        (hk ▸ Dvd.dvd.mul_left (Nat.minFac_dvd k) p)
  · rintro ⟨p, hp, hpn, hpp, hmin⟩
    exact lt_F_of_witness hp hpn hpp hmin

/-- Odd `n ≥ 7` is never an exception: take `p = 2`. -/
theorem lt_F_of_odd {n : ℕ} (hn : 7 ≤ n) (hodd : n % 2 = 1) : n < F n := by
  apply lt_F_of_witness Nat.prime_two (by omega) (by omega)
  exact (Nat.minFac_prime (by omega)).two_le

/-- Even `n ≥ 6` has `n ≤ F n`: take `m = n - 2`. -/
theorem le_F_of_even {n : ℕ} (hn : 6 ≤ n) (heven : n % 2 = 0) : n ≤ F n := by
  have hmin : (n - 2).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr (by omega)
  have hval : n - 2 + (n - 2).minFac ∈ values n :=
    ⟨n - 2, by omega, by omega, fun h => by
      have := h.eq_one_or_self_of_dvd 2 (by omega); omega, rfl⟩
  have := le_F hval
  omega

/-- If `n - 1` is composite then `n` is not an exception. -/
theorem lt_F_of_not_prime_pred {n : ℕ} (hn : 5 ≤ n) (hnp : ¬ (n - 1).Prime) : n < F n := by
  have hval : n - 1 + (n - 1).minFac ∈ values n := ⟨n - 1, by omega, by omega, hnp, rfl⟩
  have := le_F hval
  have := (Nat.minFac_prime (show n - 1 ≠ 1 by omega)).two_le
  omega

/-- Every exception `n ≥ 7` is even, has `n - 1` prime, and has `F n = n`. -/
theorem exception_structure {n : ℕ} (hn : 7 ≤ n) (hF : F n ≤ n) :
    n % 2 = 0 ∧ (n - 1).Prime ∧ F n = n := by
  have heven : n % 2 = 0 := by
    by_contra h
    exact absurd (lt_F_of_odd hn (by omega)) (by omega)
  refine ⟨heven, ?_, le_antisymm hF (le_F_of_even (by omega) heven)⟩
  by_contra h
  exact absurd (lt_F_of_not_prime_pred (by omega) h) (by omega)

end Erdos430

#print axioms Erdos430.forall_terms_prime_iff
#print axioms Erdos430.erdos430_iff_erdos385_i
#print axioms Erdos430.lt_F_iff
#print axioms Erdos430.exception_structure
