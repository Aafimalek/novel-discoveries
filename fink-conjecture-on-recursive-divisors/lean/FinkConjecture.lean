import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Fink's conjecture on recursive divisors

An exponent vector encodes an integer on a fixed ordered set of distinct primes.
In the divisor recurrence, a proper divisor is the second part of an additive
split whose first part is nonzero. The weight `u` records one strict step.
-/

open scoped BigOperators
open Finset

namespace Fink

variable {R : Type*} [CommRing R]

/-- An exponent vector on an ordered alphabet of `r` prime positions. -/
abbrev Exponents (r : ℕ) := Fin r →₀ ℕ

/-- Formal series whose coefficients are indexed by prime exponents. -/
abbrev Series (R : Type*) (r : ℕ) := MvPowerSeries (Fin r) R

/-- The geometric series with coefficients `c ^ a` at degree `a`. -/
private noncomputable def geometric (c : R) : PowerSeries R :=
  PowerSeries.rescale c (PowerSeries.invOneSubPow R 1).val

/-- The scaled geometric series inverts the linear denominator. -/
private theorem geometric_mul (c : R) :
    geometric c * (1 - PowerSeries.C c * PowerSeries.X) = 1 := by
  have h := PowerSeries.mk_one_mul_one_sub_eq_one R
  have hgeom : (PowerSeries.invOneSubPow R 1).val =
      PowerSeries.mk (1 : ℕ → R) := by
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    ext n
    simp
  rw [geometric, hgeom]
  simpa only [map_mul, map_sub, map_one, PowerSeries.rescale_X] using
    congrArg (PowerSeries.rescale c) h

/-- Extracting a coefficient from a positive power gives a scaled binomial. -/
private theorem coeff_geometric_pow (c : R) (a s : ℕ) :
    PowerSeries.coeff a (geometric c ^ (s + 1)) =
      c ^ a * (Nat.choose (s + a) s : R) := by
  have hpow (m : ℕ) : (PowerSeries.invOneSubPow R 1) ^ m =
      PowerSeries.invOneSubPow R m := by
    induction m with
    | zero => simp [PowerSeries.invOneSubPow_zero]
    | succ m ih =>
      rw [pow_succ, ih, ← PowerSeries.invOneSubPow_add]
  rw [geometric, ← map_pow, ← Units.val_pow_eq_pow_val, hpow,
    PowerSeries.coeff_rescale, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.coeff_mk]

/-- The series for one unrestricted exponent vector has every coefficient 1. -/
private noncomputable def box (r : ℕ) : Series R r :=
  fun _ => 1

/-- Read a coefficient of the unrestricted series. -/
@[simp] private theorem coeff_box {r : ℕ} (a : Exponents r) :
    MvPowerSeries.coeff a (box r : Series R r) = 1 := by
  rfl

/-- The unrestricted series has constant coefficient one as well. -/
@[simp] private theorem constantCoeff_box (r : ℕ) :
    MvPowerSeries.constantCoeff (box r : Series R r) = 1 := by
  rfl

/-- With zero prime positions the only exponent vector is zero. -/
private theorem box_zero : (box 0 : Series R 0) = 1 := by
  apply MvPowerSeries.ext
  intro a
  have ha : a = 0 := by
    ext j
    exact Fin.elim0 j
  simp [ha, MvPowerSeries.coeff_one]

/-- Separate the first unrestricted exponent using the first-variable equivalence. -/
private theorem box_succ (r : ℕ) :
    MvPowerSeries.finSuccEquiv R r (box (r + 1)) =
      PowerSeries.C (box r) * geometric 1 := by
  apply PowerSeries.ext
  intro a
  apply MvPowerSeries.ext
  intro b
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, PowerSeries.coeff_C_mul]
  have h := coeff_geometric_pow (1 : Series R r) a 0
  simp at h
  simp [h]

/-- Nested construction of the chain series, one prime position at a time. -/
noncomputable def chainSeries (u : R) : (r : ℕ) → Series R r
  | 0 => 1
  | r + 1 =>
    (MvPowerSeries.finSuccEquiv R r).symm
      (PowerSeries.C (chainSeries u r) *
        geometric (1 + MvPowerSeries.C u * chainSeries u r))

/-- Separate the first variable of the chain series. -/
private theorem chainSeries_succ (u : R) (r : ℕ) :
    MvPowerSeries.finSuccEquiv R r (chainSeries u (r + 1)) =
      PowerSeries.C (chainSeries u r) *
        geometric (1 + MvPowerSeries.C u * chainSeries u r) := by
  simp [chainSeries]

/-- Clear the two geometric denominators when extending the recurrence
by one variable. Keeping this in an abstract ring isolates the algebra. -/
private theorem extend_recurrence {S : Type*} [CommRing S] (c d f g h x : S)
    (hd : g * (1 - x) = 1)
    (hf : h * (1 - (1 + c * f) * x) = 1)
    (hi : (1 - c * (d - 1)) * f = d) :
    (1 - c * (d * g - 1)) * (f * h) = d * g := by
  have hclear :
      (1 - x) * ((1 - c * (d * g - 1)) * (f * h) - d * g) = 0 := by
    linear_combination
      (-(c * f * h + 1) * d) * hd + d * hf + (h * (1 - x)) * hi
  have hcancel := congrArg (g * ·) hclear
  rwa [← mul_assoc, hd, one_mul, mul_zero, sub_eq_zero] at hcancel

/-- The nested construction solves the divisor recurrence in the series ring. -/
private theorem chainSeries_mul (u : R) (r : ℕ) :
    (1 - MvPowerSeries.C u * (box r - 1)) * chainSeries u r = box r := by
  induction r with
  | zero => simp [box_zero, chainSeries]
  | succ r ih =>
    apply (MvPowerSeries.finSuccEquiv R r).injective
    simp only [map_mul, map_sub, map_one, MvPowerSeries.finSuccEquiv_C,
      box_succ, chainSeries_succ]
    have hd := geometric_mul (1 : Series R r)
    simp only [map_one, one_mul] at hd
    have hf := geometric_mul (1 + MvPowerSeries.C u * chainSeries u r)
    simp only [map_add, map_one, map_mul] at hf
    have hi := congrArg (PowerSeries.C (R := Series R r)) ih
    simp only [map_mul, map_sub, map_one] at hi
    exact extend_recurrence (PowerSeries.C (MvPowerSeries.C u)) (PowerSeries.C (box r))
      (PowerSeries.C (chainSeries u r)) (geometric (1 : Series R r))
      (geometric (1 + MvPowerSeries.C u * chainSeries u r)) PowerSeries.X hd hf hi

/-- The weighted nested binomial sum, with `s` selected indices so far. -/
noncomputable def binomialSum (u : R) : (r : ℕ) → ℕ → Exponents r → R
  | 0, _, _ => 1
  | r + 1, s, a =>
    ∑ i ∈ range (a 0 + 1),
      (Nat.choose (a 0 + s) (a 0) : R) * (Nat.choose (a 0) i : R) * u ^ i *
        binomialSum u r (s + i) (Finsupp.tail a)

/-- Multiplying the peeled series out gives the next nested binomial sum. -/
private theorem coeff_chainSeries_pow (u : R) (r s : ℕ) (a : Exponents r) :
    MvPowerSeries.coeff a (chainSeries u r ^ (s + 1)) =
      binomialSum u r s a := by
  induction r generalizing s with
  | zero =>
    have ha : a = 0 := by
      ext j
      exact Fin.elim0 j
    simp [ha, chainSeries, binomialSum, MvPowerSeries.coeff_one]
  | succ r ih =>
    let f := chainSeries u r
    let c : Series R r := MvPowerSeries.C u
    rw [← Finsupp.cons_tail a, ← MvPowerSeries.coeff_coeff_finSuccEquiv]
    rw [map_pow, chainSeries_succ, mul_pow, ← map_pow, PowerSeries.coeff_C_mul,
      coeff_geometric_pow]
    -- Expand the only remaining binomial in the smaller series ring.
    change MvPowerSeries.coeff (Finsupp.tail a)
      (f ^ (s + 1) * ((1 + c * f) ^ a 0 * (Nat.choose (s + a 0) s : Series R r))) =
        binomialSum u (r + 1) s (Finsupp.cons (a 0) (Finsupp.tail a))
    rw [add_comm (1 : Series R r), add_pow]
    simp only [one_pow, mul_one, mul_pow, Finset.sum_mul, Finset.mul_sum, map_sum,
      binomialSum, Finsupp.cons_zero, Finsupp.tail_cons]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Nat.choose (s + a 0) s = Nat.choose (a 0 + s) (a 0) by
      rw [Nat.add_comm s, Nat.choose_symm_add]]
    let b := Finsupp.tail a
    let m := Nat.choose (a 0 + s) (a 0)
    let n := Nat.choose (a 0) i
    have hterm :
        f ^ (s + 1) * (c ^ i * f ^ i * (n : Series R r) * (m : Series R r)) =
          MvPowerSeries.C ((m : R) * (n : R) * u ^ i) * f ^ (s + i + 1) := by
      simp only [map_mul, map_pow, map_natCast, c]
      rw [show s + i + 1 = s + 1 + i by omega, pow_add]
      ring
    change MvPowerSeries.coeff b
      (f ^ (s + 1) * (c ^ i * f ^ i * (n : Series R r) * (m : Series R r))) =
        (m : R) * (n : R) * u ^ i * binomialSum u r (s + i) b
    rw [hterm, MvPowerSeries.coeff_C_mul, ih]

/-- Evaluate the proper-divisor sum in exponent coordinates. A split
`(q,b)` of `a` encodes the quotient and divisor, and `q = 0` is skipped. -/
noncomputable def properSum {r : ℕ} (f : Exponents r → R) (a : Exponents r) : R :=
  ∑ p ∈ antidiagonal a, if p.1 = 0 then 0 else f p.2

/-- The coefficient on a proper split comes from the unrestricted series minus 1. -/
private theorem coeff_box_sub_one_mul {r : ℕ} (f : Series R r) (a : Exponents r) :
    MvPowerSeries.coeff a ((box r - 1) * f) =
      properSum (fun b => MvPowerSeries.coeff b f) a := by
  rw [MvPowerSeries.coeff_mul, properSum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.1 = 0 <;> simp [h, MvPowerSeries.coeff_one]

/-- Fink's full weighted identity for any function satisfying the strict
divisor recurrence on exponent vectors. Take `u = 1` for the conjecture,
or `u = Polynomial.X` to count chains by length. -/
theorem conjecture_of_recurrence {r : ℕ} (u : R) (f : Exponents r → R)
    (hf : ∀ a, f a = 1 + u * properSum f a) (a : Exponents r) :
    f a = binomialSum u r 0 a := by
  let series : Series R r := f
  have hrec : series = box r + MvPowerSeries.C u * ((box r - 1) * series) := by
    apply MvPowerSeries.ext
    intro b
    rw [map_add, coeff_box, MvPowerSeries.coeff_C_mul, coeff_box_sub_one_mul]
    exact hf b
  have hseries : (1 - MvPowerSeries.C u * (box r - 1)) * series = box r := by
    rw [sub_mul, one_mul, mul_assoc]
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hrec)
  have hunit : IsUnit (1 - MvPowerSeries.C u * (box r - 1) : Series R r) := by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    simp
  have heq : series = chainSeries u r := hunit.mul_left_cancel
    (hseries.trans (chainSeries_mul u r).symm)
  calc
    f a = MvPowerSeries.coeff a series := rfl
    _ = MvPowerSeries.coeff a (chainSeries u r ^ (0 + 1)) := by
      simpa using congrArg (MvPowerSeries.coeff a) heq
    _ = binomialSum u r 0 a := coeff_chainSeries_pow u r 0 a

/-- Encode an exponent vector by multiplying the specified prime powers. -/
noncomputable def encode {r : ℕ} (primes : Fin r ↪ ℕ) (a : Exponents r) : ℕ :=
  (a.embDomain primes).prod (· ^ ·)

/-- Every index in the transported support is an encoded prime position. -/
private theorem support_encode {r : ℕ} (primes : Fin r ↪ ℕ) (a : Exponents r) :
    (↑(a.embDomain primes).support : Set ℕ) ⊆ Set.range primes := by
  intro p hp
  have hp' : p ∈ (a.embDomain primes).support := Finset.mem_coe.mp hp
  rw [Finsupp.support_embDomain] at hp'
  rcases Finset.mem_map.mp hp' with ⟨i, _, rfl⟩
  exact ⟨i, rfl⟩

/-- For actual primes, the transported vector is the natural factorization. -/
theorem factorization_encode {r : ℕ} (primes : Fin r ↪ ℕ)
    (hp : ∀ i, (primes i).Prime) (a : Exponents r) :
    (encode primes a).factorization = a.embDomain primes := by
  apply Nat.factorization_prod_pow_eq_self
  intro p h
  obtain ⟨i, rfl⟩ := support_encode primes a h
  exact hp i

/-- A product of powers of primes is nonzero, including the empty product. -/
private theorem encode_ne_zero {r : ℕ} (primes : Fin r ↪ ℕ)
    (hp : ∀ i, (primes i).Prime) (a : Exponents r) : encode primes a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p h
  obtain ⟨i, rfl⟩ := support_encode primes a h
  exact pow_ne_zero _ (hp i).ne_zero

/-- A nonzero quotient exponent vector corresponds to a proper divisor.
The sum is transported by the bijection from exponent splits to divisors. -/
private theorem properSum_encode {r : ℕ} (primes : Fin r ↪ ℕ)
    (hp : ∀ i, (primes i).Prime) (f : ℕ → R) (a : Exponents r) :
    properSum (fun b => f (encode primes b)) a =
      ∑ d ∈ (encode primes a).properDivisors, f d := by
  classical
  have hencode : Function.Injective (encode primes) := by
    intro x y h
    apply Finsupp.embDomain_injective primes
    simpa only [factorization_encode primes hp] using congrArg Nat.factorization h
  have ha := encode_ne_zero primes hp a
  calc
    _ = ∑ p ∈ (antidiagonal a).filter (fun p => p.1 ≠ 0), f (encode primes p.2) := by
      simp [properSum, Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_bij (fun p _ => encode primes p.2)
      · intro p h
        obtain ⟨hs, hq⟩ := Finset.mem_filter.mp h
        have hsplit := Finset.mem_antidiagonal.mp hs
        have hb : p.2 ≤ a := by
          rw [← hsplit]
          exact le_add_self
        have hd : encode primes p.2 ∣ encode primes a := by
          apply (Nat.factorization_le_iff_dvd (encode_ne_zero primes hp p.2) ha).mp
          simpa [factorization_encode primes hp, Finsupp.embDomain_le_embDomain_iff_le]
        refine Nat.mem_properDivisors.mpr ⟨hd, lt_of_le_of_ne (Nat.le_of_dvd
          (Nat.pos_of_ne_zero ha) hd) ?_⟩
        intro he
        apply hq
        have hba := hencode he
        exact add_right_cancel (show p.1 + p.2 = 0 + p.2 by simpa [hba] using hsplit)
      · intro x hx y hy he
        have hb := hencode he
        have hsx := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hx).1
        have hsy := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hy).1
        have hsum : x.1 + x.2 = y.1 + x.2 := by rw [hsx, hb, hsy]
        exact Prod.ext (add_right_cancel hsum) hb
      · intro d hd
        have hnat := Nat.mem_properDivisors.mp hd
        have hdne := (Nat.pos_of_mem_properDivisors hd).ne'
        have hle : d.factorization ≤ a.embDomain primes := by
          rw [← factorization_encode primes hp]
          exact (Nat.factorization_le_iff_dvd hdne ha).mpr hnat.1
        let b : Exponents r := d.factorization.comapDomain primes primes.injective.injOn
        have hem : b.embDomain primes = d.factorization :=
          Finsupp.embDomain_comapDomain (fun _ h =>
            support_encode primes a (Finsupp.support_mono hle h))
        have heq : encode primes b = d := by
          rw [encode, hem, Nat.prod_factorization_pow_eq_self hdne]
        have hba : b < a := lt_of_le_of_ne
          ((Finsupp.embDomain_le_embDomain_iff_le primes b a).mp (hem ▸ hle))
          (fun h => hnat.2.ne (heq.symm.trans (congrArg (encode primes) h)))
        refine ⟨(a - b, b), Finset.mem_filter.mpr ⟨?_, ?_⟩, heq⟩
        · exact Finset.mem_antidiagonal.mpr (tsub_add_cancel_of_le hba.le)
        · exact fun h => (not_le_of_gt hba) (tsub_eq_zero_iff_le.mp h)
      · intro _ _
        rfl

/-- The divisor-chain polynomial specialized at a weight `u`. The
zero-step chain contributes one, and a first proper divisor contributes `u`. -/
noncomputable def divisorChains (u : R) (n : ℕ) : R :=
  1 + u * ∑ d ∈ n.properDivisors.attach, divisorChains u d.val
termination_by n
decreasing_by
  exact (Nat.mem_properDivisors.mp d.property).2

/-- The defining recurrence with the attached membership proofs removed. -/
theorem divisorChains_rec (u : R) (n : ℕ) :
    divisorChains u n = 1 + u * ∑ d ∈ n.properDivisors, divisorChains u d := by
  rw [divisorChains, Finset.sum_attach]

/-- Fink's identity for the actual proper divisors of a product of prime
powers. This also proves its chain-length refinement over `ℤ[X]`. -/
theorem divisorChains_identity {r : ℕ} (u : R) (primes : Fin r ↪ ℕ)
    (hp : ∀ i, (primes i).Prime) (a : Exponents r) :
    divisorChains u (encode primes a) = binomialSum u r 0 a := by
  apply conjecture_of_recurrence u (fun b => divisorChains u (encode primes b)) _ a
  intro b
  rw [properSum_encode primes hp, divisorChains_rec]

/-! ## The printed form of Conjecture 1

Fink states the conjecture with the last index summed out, which gives the
factor `2 ^ α_ω`. `finkSum` is that printed form in exponent coordinates:
position `0` plays the role of `α₁`, and the last position contributes
`2 ^ α_ω` times its single remaining binomial. -/

/-- Fink's printed nested sum, with `s` selected indices so far. -/
noncomputable def finkSum : (r : ℕ) → ℕ → Exponents r → ℕ
  | 0, _, _ => 1
  | 1, s, a => Nat.choose (a 0 + s) (a 0) * 2 ^ a 0
  | r + 2, s, a =>
    ∑ i ∈ range (a 0 + 1),
      Nat.choose (a 0 + s) (a 0) * Nat.choose (a 0) i *
        finkSum (r + 1) (s + i) (Finsupp.tail a)

/-- At `u = 1` the symmetric sum equals the printed sum: the last index
only appears in `choose α_ω i_ω`, which sums to `2 ^ α_ω`. -/
theorem binomialSum_one_eq_finkSum (r s : ℕ) (a : Exponents (r + 1)) :
    binomialSum (1 : ℤ) (r + 1) s a = (finkSum (r + 1) s a : ℤ) := by
  induction r generalizing s with
  | zero =>
    simp only [binomialSum, one_pow, mul_one, finkSum, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    rw [← Finset.mul_sum]
    congr 1
    exact_mod_cast Nat.sum_range_choose (a 0)
  | succ r ih =>
    rw [binomialSum, finkSum]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [one_pow, mul_one, ih]

/-- **Fink's Conjecture 1.** For `n = p₁ ^ α₁ ⋯ p_ω ^ α_ω` with `ω ≥ 1`, the
number of recursive divisors `κ₀(n)` (here `divisorChains 1 n`) equals
Fink's printed nested binomial sum. -/
theorem fink_conjecture_1 {r : ℕ} (primes : Fin (r + 1) ↪ ℕ)
    (hp : ∀ i, (primes i).Prime) (a : Exponents (r + 1)) :
    divisorChains (1 : ℤ) (encode primes a) = (finkSum (r + 1) 0 a : ℤ) := by
  rw [divisorChains_identity 1 primes hp a, binomialSum_one_eq_finkSum]

/-! ## A concrete check of the definitions

`κ₀(12) = 16`, computed straight from the recurrence. The chain polynomial
is `C₁₂(u) = 1 + 5u + 7u² + 3u³`, whose value at `u = 1` is 16. -/

private theorem divisorChains_one : divisorChains (1 : ℤ) 1 = 1 := by
  rw [divisorChains_rec]; simp

private theorem divisorChains_prime {p : ℕ} (hp : p.Prime) :
    divisorChains (1 : ℤ) p = 2 := by
  rw [divisorChains_rec, Nat.Prime.properDivisors hp]
  simp [divisorChains_one]

example : divisorChains (1 : ℤ) 12 = 16 := by
  have h4 : divisorChains (1 : ℤ) 4 = 4 := by
    rw [divisorChains_rec, show Nat.properDivisors 4 = {1, 2} by decide]
    simp [divisorChains_one, divisorChains_prime Nat.prime_two]
  have h6 : divisorChains (1 : ℤ) 6 = 6 := by
    rw [divisorChains_rec, show Nat.properDivisors 6 = {1, 2, 3} by decide]
    simp [divisorChains_one, divisorChains_prime Nat.prime_two,
      divisorChains_prime Nat.prime_three]
  rw [divisorChains_rec, show Nat.properDivisors 12 = {1, 2, 3, 4, 6} by decide]
  simp [divisorChains_one, divisorChains_prime Nat.prime_two,
    divisorChains_prime Nat.prime_three, h4, h6]

end Fink

#print axioms Fink.divisorChains_identity
#print axioms Fink.fink_conjecture_1
