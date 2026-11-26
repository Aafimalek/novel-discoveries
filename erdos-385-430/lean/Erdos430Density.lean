import Erdos430
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# Erdős Problem 385(ii) holds for almost all `n`

For every fixed `T`, the integers `n` with `F n ≤ n + T` have natural density zero
(`density_F_le_add`). The proof is a second-moment argument over residues.

* Fix `J ≥ 1`, put `z = 2J + T`, and let `P` be the primes up to `z`. For a choice of one
  residue modulo each prime in `P`, `S` counts the shifts `j ∈ [J, 2J]` that avoid all of them.
  For `n` this counts the `n - j` with no prime factor up to `z`.
* If `F n ≤ n + T` and no `n - j` is prime, then `S = 0`, since a composite `n - j` with least
  prime factor above `z` would push `F n` above `n + T`.
* Exact counting on the product space gives `Var S ≤ E S` (`card_S_eq_zero_le`). The only
  inequality needed is a bound for pairs in an interval whose difference is divisible by `m`,
  and the products over primes collapse because `(q - 2) + 1 / q = (q - 1) ^ 2 / q`.
* The residues of `n` modulo the primes of `P` take each value at most once on any block of
  `primorial z` consecutive integers, so counts transfer from the product space to `[0, X)`.

The finite inequality `card_F_le_add_le` holds for all `X`, `T` and `J`; the density
statement follows from `π(x) = o(x)`, which comes from Chebyshev's bound in mathlib.
Letting `J` and `T` grow with `X` gives `density_F_le_add_of_tendsto`: the threshold `T` may
grow like any `o(log X)`. The method stops near `log X` because it counts over whole periods
of the primorial of `2J + T`, which must not exceed `X`.
-/

open Finset Filter Topology

namespace Erdos430

/-! ### Pairs in an interval whose difference is divisible by `m` -/

/-- An interval of `L` integers meets each residue class modulo `m` at most
`(L - 1) / m + 1` times. -/
theorem card_class_le (a : ℤ) (L m : ℕ) (hm : 0 < m) (j : ℤ) :
    #{x ∈ Ico a (a + L) | (m : ℤ) ∣ j - x} ≤ (L - 1) / m + 1 := by
  set A := (Ico a (a + L)).filter (fun x => (m : ℤ) ∣ j - x) with hA
  rcases A.eq_empty_or_nonempty with h | hne
  · rw [h]; simp
  set c := A.min' hne
  have hc : c ∈ A := A.min'_mem hne
  have hsub : A ⊆ (range ((L - 1) / m + 1)).image (fun t : ℕ => c + (t : ℤ) * m) := by
    intro x hx
    have hcx : c ≤ x := A.min'_le x hx
    simp only [hA, mem_filter, mem_Ico] at hx hc
    obtain ⟨⟨hax, hxL⟩, hdx⟩ := hx
    obtain ⟨⟨hac, hcL⟩, hdc⟩ := hc
    obtain ⟨t, ht⟩ : (m : ℤ) ∣ x - c := by
      have := dvd_sub hdc hdx
      rwa [show j - c - (j - x) = x - c by ring] at this
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    have ht0 : 0 ≤ t := by nlinarith
    refine mem_image.mpr ⟨t.toNat, ?_, ?_⟩
    · rw [mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hm]
      have hle : (t.toNat : ℤ) * m ≤ (L : ℤ) - 1 := by
        rw [Int.toNat_of_nonneg ht0]; nlinarith
      omega
    · rw [Int.toNat_of_nonneg ht0]; linarith
  calc #A ≤ #((range ((L - 1) / m + 1)).image (fun t : ℕ => c + (t : ℤ) * m)) :=
        card_le_card hsub
    _ ≤ #(range ((L - 1) / m + 1)) := card_image_le
    _ = (L - 1) / m + 1 := card_range _

/-- Each point of an interval of `L` integers has at most `(L - 1) / m` partners `j' ≠ j` in
the interval with `m ∣ j - j'`. -/
theorem card_partners_le (a : ℤ) (L m : ℕ) (hm : 0 < m) (j : ℤ) (hj : j ∈ Ico a (a + L)) :
    (#{j' ∈ Ico a (a + L) | j' ≠ j ∧ (m : ℤ) ∣ j - j'} : ℝ) ≤ ((L : ℝ) - 1) / m := by
  have hset : (Ico a (a + L)).filter (fun j' => j' ≠ j ∧ (m : ℤ) ∣ j - j') =
      ((Ico a (a + L)).filter (fun x => (m : ℤ) ∣ j - x)).erase j := by
    ext x; simp [mem_erase, and_comm, and_left_comm]
  have hmem : j ∈ (Ico a (a + L)).filter (fun x => (m : ℤ) ∣ j - x) := by
    simp [hj]
  have hL : 1 ≤ L := by
    rw [mem_Ico] at hj; omega
  have hnat : #{j' ∈ Ico a (a + L) | j' ≠ j ∧ (m : ℤ) ∣ j - j'} ≤ (L - 1) / m := by
    rw [hset, card_erase_of_mem hmem]
    exact Nat.sub_le_iff_le_add.mpr (card_class_le a L m hm j)
  calc (#{j' ∈ Ico a (a + L) | j' ≠ j ∧ (m : ℤ) ∣ j - j'} : ℝ)
      ≤ (((L - 1) / m : ℕ) : ℝ) := by exact_mod_cast hnat
    _ ≤ ((L - 1 : ℕ) : ℝ) / m := Nat.cast_div_le
    _ = ((L : ℝ) - 1) / m := by rw [Nat.cast_sub hL]; simp

/-- Summing over the interval: at most `L (L - 1) / m` ordered pairs `j ≠ j'` with
`m ∣ j - j'`. -/
theorem sum_partners_le (a : ℤ) (L m : ℕ) (hm : 0 < m) :
    ∑ j ∈ Ico a (a + L), (#{j' ∈ Ico a (a + L) | j' ≠ j ∧ (m : ℤ) ∣ j - j'} : ℝ) ≤
      (L : ℝ) * ((L : ℝ) - 1) / m := by
  calc ∑ j ∈ Ico a (a + L), (#{j' ∈ Ico a (a + L) | j' ≠ j ∧ (m : ℤ) ∣ j - j'} : ℝ)
      ≤ ∑ _j ∈ Ico a (a + L), ((L : ℝ) - 1) / m :=
        sum_le_sum fun j hj => card_partners_le a L m hm j hj
    _ = (L : ℝ) * ((L : ℝ) - 1) / m := by
        rw [sum_const, Int.card_Ico, show a + L - a = (L : ℤ) by ring, Int.toNat_natCast,
          nsmul_eq_mul]
        ring

/-! ### The pair sum over primes -/

/-- If every prime of `s` divides `d`, so does their product. -/
theorem prod_dvd_of_forall_dvd {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) {d : ℤ}
    (h : ∀ q ∈ s, (q : ℤ) ∣ d) : ((∏ q ∈ s, q : ℕ) : ℤ) ∣ d := by
  push_cast
  apply Finset.prod_dvd_of_coprime _ h
  intro q hq r hr hqr
  exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hs q hq) (hs r hr)).mpr hqr)

/-- The number of residue choices avoiding both `j` and `j'`, written so that it expands
over subsets: modulo `q` there are `q - 2` choices, plus one more when `q ∣ j - j'`. -/
def pairWeight (P : Finset ℕ) (d : ℤ) : ℝ :=
  ∏ q ∈ P, ((if (q : ℤ) ∣ d then 1 else 0) + ((q : ℝ) - 2))

/-- **The pair-sum bound.** Summed over ordered pairs of distinct points of an interval of
length `L`, the pair weights total at most `L (L - 1) ∏ (q - 1)^2 / q`. -/
theorem sum_pairWeight_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (a : ℤ) (L : ℕ) :
    ∑ j ∈ Ico a (a + L), ∑ j' ∈ (Ico a (a + L)).filter (· ≠ j), pairWeight P (j - j') ≤
      (L : ℝ) * ((L : ℝ) - 1) * ∏ q ∈ P, (((q : ℝ) - 1) ^ 2 / q) := by
  classical
  have hq2 : ∀ q ∈ P, (0 : ℝ) ≤ (q : ℝ) - 2 := fun q hq => by
    have := (hP q hq).two_le
    have : (2 : ℝ) ≤ q := by exact_mod_cast this
    linarith
  -- Expand each weight over subsets of `P`.
  have hexp : ∀ d : ℤ, pairWeight P d ≤
      ∑ s ∈ P.powerset, (if ((∏ q ∈ s, q : ℕ) : ℤ) ∣ d then 1 else 0) *
        ∏ q ∈ P \ s, ((q : ℝ) - 2) := by
    intro d
    rw [pairWeight, prod_add]
    refine sum_le_sum fun s hs => ?_
    have hsP : s ⊆ P := mem_powerset.mp hs
    apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun q hq => hq2 q (mem_sdiff.mp hq).1)
    by_cases hall : ∀ q ∈ s, (q : ℤ) ∣ d
    · rw [if_pos (prod_dvd_of_forall_dvd (fun q hq => hP q (hsP hq)) hall)]
      rw [prod_congr rfl fun q hq => if_pos (hall q hq)]
      simp
    · push_neg at hall
      obtain ⟨q, hq, hqd⟩ := hall
      rw [prod_eq_zero hq (if_neg hqd)]
      split_ifs <;> norm_num
  have hpos : ∀ s ∈ P.powerset, 0 < ∏ q ∈ s, q := fun s hs =>
    prod_pos fun q hq => (hP q (mem_powerset.mp hs hq)).pos
  calc ∑ j ∈ Ico a (a + L), ∑ j' ∈ (Ico a (a + L)).filter (· ≠ j), pairWeight P (j - j')
      ≤ ∑ j ∈ Ico a (a + L), ∑ j' ∈ (Ico a (a + L)).filter (· ≠ j),
          ∑ s ∈ P.powerset, (if ((∏ q ∈ s, q : ℕ) : ℤ) ∣ j - j' then 1 else 0) *
            ∏ q ∈ P \ s, ((q : ℝ) - 2) :=
        sum_le_sum fun j _ => sum_le_sum fun j' _ => hexp _
    _ = ∑ j ∈ Ico a (a + L), ∑ s ∈ P.powerset, ∑ j' ∈ (Ico a (a + L)).filter (· ≠ j),
          (if ((∏ q ∈ s, q : ℕ) : ℤ) ∣ j - j' then 1 else 0) * ∏ q ∈ P \ s, ((q : ℝ) - 2) :=
        sum_congr rfl fun j _ => sum_comm
    _ = ∑ s ∈ P.powerset, ∑ j ∈ Ico a (a + L), ∑ j' ∈ (Ico a (a + L)).filter (· ≠ j),
          (if ((∏ q ∈ s, q : ℕ) : ℤ) ∣ j - j' then 1 else 0) * ∏ q ∈ P \ s, ((q : ℝ) - 2) :=
        sum_comm
    _ = ∑ s ∈ P.powerset, (∏ q ∈ P \ s, ((q : ℝ) - 2)) *
          ∑ j ∈ Ico a (a + L),
            (#{j' ∈ Ico a (a + L) | j' ≠ j ∧ ((∏ q ∈ s, q : ℕ) : ℤ) ∣ j - j'} : ℝ) := by
        refine sum_congr rfl fun s _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [← filter_filter, ← sum_boole, mul_sum]
        exact sum_congr rfl fun j' _ => mul_comm _ _
    _ ≤ ∑ s ∈ P.powerset, (∏ q ∈ P \ s, ((q : ℝ) - 2)) *
          ((L : ℝ) * ((L : ℝ) - 1) / (∏ q ∈ s, q : ℕ)) := by
        refine sum_le_sum fun s hs => mul_le_mul_of_nonneg_left
          (sum_partners_le a L _ (hpos s hs)) (prod_nonneg fun q hq => hq2 q (mem_sdiff.mp hq).1)
    _ = (L : ℝ) * ((L : ℝ) - 1) * ∑ s ∈ P.powerset,
          (∏ q ∈ s, (1 / (q : ℝ))) * ∏ q ∈ P \ s, ((q : ℝ) - 2) := by
        rw [mul_sum]
        refine sum_congr rfl fun s _ => ?_
        push_cast
        rw [prod_div_distrib, prod_const_one]
        ring
    _ = (L : ℝ) * ((L : ℝ) - 1) * ∏ q ∈ P, (((q : ℝ) - 1) ^ 2 / q) := by
        rw [← prod_add]
        congr 1
        refine prod_congr rfl fun q hq => ?_
        have : (q : ℝ) ≠ 0 := by exact_mod_cast (hP q hq).ne_zero
        field_simp
        ring

/-! ### Counting on the product space `∏ ℤ/q` -/

section ProductSpace

variable (P : Finset ℕ) [hP0 : ∀ q : P, NeZero (q : ℕ)]

/-- One residue modulo each prime of `P`. -/
abbrev Omega := (q : P) → ZMod q

/-- `ω` avoids the shift `j`: no residue of `ω` equals `j`. -/
def Avoids (ω : Omega P) (j : ℤ) : Prop := ∀ q : P, ω q ≠ (j : ZMod q)

instance (ω : Omega P) (j : ℤ) : Decidable (Avoids P ω j) := by
  unfold Avoids; infer_instance

/-- The number of shifts in `I` avoided by `ω`. -/
def S (I : Finset ℤ) (ω : Omega P) : ℕ := #{j ∈ I | Avoids P ω j}

theorem card_omega : Fintype.card (Omega P) = ∏ q ∈ P, q := by
  rw [Fintype.card_pi, ← prod_coe_sort P]
  exact prod_congr rfl fun q _ => ZMod.card q

theorem card_avoids (j : ℤ) :
    #{ω : Omega P | Avoids P ω j} = ∏ q ∈ P, (q - 1) := by
  have : (univ.filter fun ω : Omega P => Avoids P ω j) =
      Fintype.piFinset fun q : P => univ.erase (j : ZMod q) := by
    ext ω; simp [Avoids, Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset, ← prod_coe_sort P]
  refine prod_congr rfl fun q _ => ?_
  rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

theorem card_avoids_pair (j j' : ℤ) (hP : ∀ q ∈ P, q.Prime) :
    (#{ω : Omega P | Avoids P ω j ∧ Avoids P ω j'} : ℝ) = pairWeight P (j - j') := by
  have : (univ.filter fun ω : Omega P => Avoids P ω j ∧ Avoids P ω j') =
      Fintype.piFinset fun q : P => (univ.erase (j : ZMod q)).erase (j' : ZMod q) := by
    ext ω; simp [Avoids, Fintype.mem_piFinset, forall_and, and_comm]
  rw [this, Fintype.card_piFinset, pairWeight, ← prod_coe_sort P, Nat.cast_prod]
  refine prod_congr rfl fun q _ => ?_
  have hq2 := (hP q q.2).two_le
  by_cases h : (j' : ZMod q) = (j : ZMod q)
  · have hd : ((q : ℕ) : ℤ) ∣ j - j' := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
    rw [if_pos hd, h, erase_eq_of_notMem (notMem_erase _ _), card_erase_of_mem (mem_univ _),
      card_univ, ZMod.card, Nat.cast_sub (by omega)]
    ring
  · have hd : ¬ ((q : ℕ) : ℤ) ∣ j - j' := fun hd =>
      h ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hd)
    rw [if_neg hd, card_erase_of_mem (mem_erase.mpr ⟨h, mem_univ _⟩),
      card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
    push_cast [Nat.cast_sub (show 1 ≤ (q : ℕ) by omega),
      Nat.cast_sub (show 1 ≤ (q : ℕ) - 1 by omega)]
    ring

/-- **`Var S ≤ E S`, in counting form.** Few residue choices avoid no shift of an interval:
at most `Q ^ 2 / (L N)` of the `Q` choices, where `N = ∏ (q - 1)`. -/
theorem card_S_eq_zero_le (hP : ∀ q ∈ P, q.Prime) (a : ℤ) (L : ℕ) (hL : 1 ≤ L) :
    (#{ω : Omega P | S P (Ico a (a + L)) ω = 0} : ℝ) ≤
      ((∏ q ∈ P, q : ℕ) : ℝ) ^ 2 / ((L : ℝ) * (∏ q ∈ P, (q - 1) : ℕ)) := by
  classical
  set I := Ico a (a + L) with hI
  set Q : ℝ := ((∏ q ∈ P, q : ℕ) : ℝ) with hQ
  set N : ℝ := ((∏ q ∈ P, (q - 1) : ℕ) : ℝ) with hN
  have hQpos : 0 < Q := by
    rw [hQ]; exact_mod_cast prod_pos fun q hq => (hP q hq).pos
  have hNpos : 0 < N := by
    rw [hN]; exact_mod_cast prod_pos fun q hq => Nat.sub_pos_of_lt (hP q hq).one_lt
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hcardI : #I = L := by
    rw [hI, Int.card_Ico, show a + L - a = (L : ℤ) by ring, Int.toNat_natCast]
  have hcardΩ : (Fintype.card (Omega P) : ℝ) = Q := by rw [card_omega]
  -- `S` as a sum of indicators.
  have hSsum : ∀ ω : Omega P, (S P I ω : ℝ) = ∑ j ∈ I, (if Avoids P ω j then (1 : ℝ) else 0) :=
    fun ω => by rw [S, sum_boole]
  -- First moment.
  have hS1 : ∑ ω : Omega P, (S P I ω : ℝ) = L * N := by
    simp_rw [hSsum]
    rw [sum_comm]
    rw [sum_congr rfl fun j _ => by rw [sum_boole, card_avoids]]
    rw [sum_const, hcardI, nsmul_eq_mul]
  -- Second moment.
  have hS2 : ∑ ω : Omega P, (S P I ω : ℝ) ^ 2 ≤
      L * N + L * (L - 1) * ∏ q ∈ P, (((q : ℝ) - 1) ^ 2 / q) := by
    have hexpand : ∀ ω : Omega P, (S P I ω : ℝ) ^ 2 =
        ∑ j ∈ I, ∑ j' ∈ I, (if Avoids P ω j ∧ Avoids P ω j' then (1 : ℝ) else 0) := by
      intro ω
      rw [hSsum, sq, sum_mul_sum]
      refine sum_congr rfl fun j _ => sum_congr rfl fun j' _ => ?_
      by_cases h1 : Avoids P ω j <;> by_cases h2 : Avoids P ω j' <;> simp [h1, h2]
    have hswap : ∑ ω : Omega P, (S P I ω : ℝ) ^ 2 =
        ∑ j ∈ I, ∑ j' ∈ I, ∑ ω : Omega P,
          (if Avoids P ω j ∧ Avoids P ω j' then (1 : ℝ) else 0) := by
      simp_rw [hexpand]
      rw [sum_comm]
      exact sum_congr rfl fun j _ => sum_comm
    have hpair : ∀ j ∈ I, ∑ j' ∈ I, ∑ ω : Omega P,
        (if Avoids P ω j ∧ Avoids P ω j' then (1 : ℝ) else 0) =
        N + ∑ j' ∈ I.filter (· ≠ j), pairWeight P (j - j') := by
      intro j hj
      rw [← add_sum_erase _ _ hj, ← filter_ne' I j]
      congr 1
      · rw [sum_boole]
        simp only [and_self]
        rw [card_avoids]
      · refine sum_congr rfl fun j' _ => ?_
        rw [sum_boole]
        exact card_avoids_pair P j j' hP
    rw [hswap, sum_congr rfl hpair, sum_add_distrib, sum_const, hcardI, nsmul_eq_mul]
    have := sum_pairWeight_le P hP a L
    rw [← hI] at this
    linarith
  -- The identity `∏ (q - 1) ^ 2 / q = N ^ 2 / Q`.
  have hNprod : N = ∏ q ∈ P, ((q : ℝ) - 1) := by
    rw [hN, Nat.cast_prod]
    exact prod_congr rfl fun q hq => by rw [Nat.cast_sub (hP q hq).one_lt.le, Nat.cast_one]
  have hQprod : Q = ∏ q ∈ P, (q : ℝ) := by rw [hQ, Nat.cast_prod]
  have hprod : ∏ q ∈ P, (((q : ℝ) - 1) ^ 2 / q) = N ^ 2 / Q := by
    rw [hNprod, hQprod, prod_div_distrib, prod_pow]
  set μ : ℝ := L * N / Q with hμ
  have hμpos : 0 < μ := by positivity
  -- Chebyshev: each residue choice with `S = 0` contributes `μ ^ 2` to the variance.
  have hvar : ∑ ω : Omega P, ((S P I ω : ℝ) - μ) ^ 2 ≤ L * N := by
    have hterm : ∀ ω : Omega P, ((S P I ω : ℝ) - μ) ^ 2 =
        (S P I ω : ℝ) ^ 2 - 2 * μ * (S P I ω : ℝ) + μ ^ 2 := fun ω => by ring
    have hexp : ∑ ω : Omega P, ((S P I ω : ℝ) - μ) ^ 2 =
        ∑ ω : Omega P, (S P I ω : ℝ) ^ 2 - 2 * μ * ∑ ω : Omega P, (S P I ω : ℝ) + Q * μ ^ 2 := by
      rw [sum_congr rfl fun ω _ => hterm ω, sum_add_distrib, sum_sub_distrib, ← mul_sum,
        sum_const, card_univ, nsmul_eq_mul, hcardΩ]
    rw [hexp, hS1]
    rw [hprod] at hS2
    have hNQ : 0 ≤ (L : ℝ) * N ^ 2 / Q := by positivity
    have hid : (L : ℝ) * (L - 1) * (N ^ 2 / Q) - 2 * μ * (L * N) + Q * μ ^ 2 =
        - ((L : ℝ) * N ^ 2 / Q) := by
      rw [hμ]; field_simp; ring
    linarith
  have hzero : (#{ω : Omega P | S P I ω = 0} : ℝ) * μ ^ 2 ≤
      ∑ ω : Omega P, ((S P I ω : ℝ) - μ) ^ 2 := by
    calc (#{ω : Omega P | S P I ω = 0} : ℝ) * μ ^ 2
        = ∑ ω ∈ univ.filter (fun ω : Omega P => S P I ω = 0), ((S P I ω : ℝ) - μ) ^ 2 := by
          rw [sum_congr rfl fun ω hω => show ((S P I ω : ℝ) - μ) ^ 2 = μ ^ 2 by
            rw [(mem_filter.mp hω).2, Nat.cast_zero]; ring]
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ ω : Omega P, ((S P I ω : ℝ) - μ) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hfinal : (#{ω : Omega P | S P I ω = 0} : ℝ) * μ ^ 2 ≤ L * N := hzero.trans hvar
  rw [le_div_iff₀ (by positivity)]
  set c : ℝ := (#{ω : Omega P | S P I ω = 0} : ℝ) with hc
  have hLN : 0 < (L : ℝ) * N := mul_pos hLpos hNpos
  have key : c * (L * N) * (L * N) ≤ Q ^ 2 * (L * N) := by
    have e : c * μ ^ 2 * Q ^ 2 = c * (L * N) * (L * N) := by rw [hμ]; field_simp
    have := mul_le_mul_of_nonneg_right hfinal (sq_nonneg Q)
    nlinarith [e]
  exact le_of_mul_le_mul_right key hLN

/-! ### From residue choices to integers -/

/-- The residues of `n` modulo the primes of `P`. -/
def res (n : ℕ) : Omega P := fun q => (n : ZMod q)

/-- Integers with equal residues modulo every prime of `P` differ by a multiple of the
product of `P`, so `res` is injective on any block of that length. -/
theorem res_injOn (hP : ∀ q ∈ P, q.Prime) (b : ℕ) :
    Set.InjOn (res P) (Ico b (b + ∏ q ∈ P, q) : Set ℕ) := by
  intro n hn n' hn' h
  simp only [coe_Ico, Set.mem_Ico] at hn hn'
  have hdvd : ∀ q ∈ P, (q : ℤ) ∣ (n : ℤ) - n' := by
    intro q hq
    have h1 := congrFun h ⟨q, hq⟩
    simp only [res] at h1
    have h2 : ((n' : ℤ) : ZMod q) = ((n : ℤ) : ZMod q) := by exact_mod_cast h1.symm
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h2
  have hprod := prod_dvd_of_forall_dvd hP (fun q hq => hdvd q hq)
  have hlt : |(n : ℤ) - n'| < ((∏ q ∈ P, q : ℕ) : ℤ) := by
    rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hprod hlt
  omega

/-- Counts transfer from residue choices to `[0, X)`: each block of length `∏ P` meets a
set of residue choices at most once per choice. -/
theorem card_res_le (hP : ∀ q ∈ P, q.Prime) (X : ℕ) (p : Omega P → Prop) [DecidablePred p] :
    #{n ∈ range X | p (res P n)} ≤ (X / ∏ q ∈ P, q + 1) * #{ω : Omega P | p ω} := by
  classical
  set Q := ∏ q ∈ P, q with hQ
  have hQpos : 0 < Q := prod_pos fun q hq => (hP q hq).pos
  have hsub : (range X).filter (fun n => p (res P n)) ⊆
      (range (X / Q + 1)).biUnion fun b => (Ico (b * Q) (b * Q + Q)).filter fun n => p (res P n) := by
    intro n hn
    rw [mem_filter, mem_range] at hn
    rw [mem_biUnion]
    refine ⟨n / Q, ?_, ?_⟩
    · rw [mem_range, Nat.lt_succ_iff]
      exact Nat.div_le_div_right hn.1.le
    · rw [mem_filter, mem_Ico]
      refine ⟨⟨Nat.div_mul_le_self n Q, ?_⟩, hn.2⟩
      have := Nat.lt_div_mul_add hQpos (a := n)
      linarith
  calc #((range X).filter fun n => p (res P n))
      ≤ #((range (X / Q + 1)).biUnion fun b =>
          (Ico (b * Q) (b * Q + Q)).filter fun n => p (res P n)) := card_le_card hsub
    _ ≤ ∑ b ∈ range (X / Q + 1), #((Ico (b * Q) (b * Q + Q)).filter fun n => p (res P n)) :=
        card_biUnion_le
    _ ≤ ∑ _b ∈ range (X / Q + 1), #{ω : Omega P | p ω} := by
        refine sum_le_sum fun b _ => card_le_card_of_injOn (res P) ?_ ?_
        · intro n hn
          rw [mem_coe, mem_filter] at hn
          rw [mem_coe, mem_filter]
          exact ⟨mem_univ _, hn.2⟩
        · intro n hn n' hn' h
          rw [mem_coe, mem_filter] at hn hn'
          exact res_injOn P hP (b * Q) (by simpa using hn.1) (by simpa using hn'.1) h
    _ = (X / Q + 1) * #{ω : Omega P | p ω} := by rw [sum_const, card_range, smul_eq_mul]

end ProductSpace

/-! ### The link to `F` -/

instance primesLE_neZero (z : ℕ) : ∀ q : Nat.primesLE z, NeZero (q : ℕ) :=
  fun q => ⟨(Nat.prime_of_mem_primesLE q.2).ne_zero⟩

/-- **The link to `F`.** If `F n ≤ n + T`, then either `n - j` is prime for some
`j ∈ [J, 2J]`, or the residues of `n` modulo the primes up to `2J + T` avoid no shift
`j ∈ [J, 2J]`. Otherwise a composite `n - j` with least prime factor above `2J + T`
would give `F n > n + T`. -/
theorem shift_witness {J T n : ℕ} (hJ : 1 ≤ J) (hn : 2 * J + 2 ≤ n) (hF : F n ≤ n + T) :
    S (Nat.primesLE (2 * J + T)) (Ico (J : ℤ) (J + (J + 1 : ℕ))) (res _ n) = 0 ∨
      ∃ k ∈ Icc J (2 * J), (n - k).Prime := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hS, hprime⟩ := hcon
  obtain ⟨j, hj⟩ := card_pos.mp (Nat.pos_of_ne_zero hS)
  rw [mem_filter, mem_Ico] at hj
  obtain ⟨⟨hjJ, hj2⟩, havoid⟩ := hj
  set k := j.toNat with hk
  have hkj : (k : ℤ) = j := Int.toNat_of_nonneg (by omega)
  have hkJ : k ∈ Icc J (2 * J) := by rw [mem_Icc]; omega
  set m := n - k with hm
  have hm2 : 2 ≤ m := by omega
  have hmp : ¬ m.Prime := hprime k hkJ
  -- No prime up to `2J + T` divides `m`.
  have hnodiv : ∀ q ∈ Nat.primesLE (2 * J + T), ¬ q ∣ m := by
    intro q hq hqm
    apply havoid ⟨q, hq⟩
    have hnk : n = m + k := by omega
    show ((n : ℕ) : ZMod q) = ((j : ℤ) : ZMod q)
    rw [← hkj, hnk, Nat.cast_add, (ZMod.natCast_eq_zero_iff m q).mpr hqm, zero_add]
    simp
  have hmin : 2 * J + T < m.minFac := by
    by_contra hle
    push Not at hle
    exact hnodiv _ (Nat.mem_primesLE.mpr ⟨hle, Nat.minFac_prime (by omega)⟩) (Nat.minFac_dvd m)
  have hval : m + m.minFac ∈ values n := ⟨m, by omega, by omega, hmp, rfl⟩
  have := le_F hval
  omega

/-- The product `∏ (1 - 1/q)` over a set of integers `≥ 2` is at least `1 / (#P + 1)`. -/
theorem prod_one_sub_inv_ge (P : Finset ℕ) (hP : ∀ q ∈ P, 2 ≤ q) :
    1 / ((#P : ℝ) + 1) ≤ ∏ q ∈ P, (1 - 1 / (q : ℝ)) := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hs2 : ∀ q ∈ s, 2 ≤ q := fun q hq => hP q (mem_insert_of_mem hq)
    have ha2 : 2 ≤ a := hP a (mem_insert_self a s)
    have hcard : #s + 2 ≤ a := by
      have hsub : s ⊆ Ico 2 a := fun q hq => mem_Ico.mpr ⟨hs2 q hq, hlt q hq⟩
      have := card_le_card hsub
      rw [Nat.card_Ico] at this
      omega
    rw [prod_insert has, card_insert_of_notMem has]
    have ih' := ih hs2
    have hapos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    have hfac : ((#s : ℝ) + 1) / (#s + 2) ≤ 1 - 1 / (a : ℝ) := by
      have hca : ((#s : ℝ) + 2) ≤ a := by exact_mod_cast hcard
      rw [div_le_iff₀ (by positivity), sub_mul, one_div, inv_mul_eq_div]
      have : ((#s : ℝ) + 2) / a ≤ 1 := (div_le_one hapos).mpr hca
      nlinarith
    calc 1 / ((((#s + 1 : ℕ)) : ℝ) + 1) = ((#s : ℝ) + 1) / (#s + 2) * (1 / ((#s : ℝ) + 1)) := by
          push_cast; field_simp; ring
      _ ≤ (1 - 1 / (a : ℝ)) * ∏ q ∈ s, (1 - 1 / (q : ℝ)) :=
          mul_le_mul hfac ih' (by positivity) (by
            have : (0 : ℝ) < 1 / a := by positivity
            have : 1 / (a : ℝ) ≤ 1 / 2 := by
              apply one_div_le_one_div_of_le (by norm_num); exact_mod_cast ha2
            linarith)

/-- `Q / N ≤ π(z) + 1` for the primes up to `z`, where `Q = ∏ q` and `N = ∏ (q - 1)`. -/
theorem prod_div_prod_sub_one_le (z : ℕ) :
    ((∏ q ∈ Nat.primesLE z, q : ℕ) : ℝ) / ((∏ q ∈ Nat.primesLE z, (q - 1) : ℕ) : ℝ) ≤
      (Nat.primeCounting z : ℝ) + 1 := by
  have hP : ∀ q ∈ Nat.primesLE z, q.Prime := fun q hq => Nat.prime_of_mem_primesLE hq
  have hratio : ((∏ q ∈ Nat.primesLE z, (q - 1) : ℕ) : ℝ) / ((∏ q ∈ Nat.primesLE z, q : ℕ) : ℝ) =
      ∏ q ∈ Nat.primesLE z, (1 - 1 / (q : ℝ)) := by
    rw [Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
    refine prod_congr rfl fun q hq => ?_
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (hP q hq).ne_zero
    rw [Nat.cast_sub (hP q hq).one_lt.le, Nat.cast_one]
    field_simp
  have hge := prod_one_sub_inv_ge (Nat.primesLE z) fun q hq => (hP q hq).two_le
  rw [← hratio, Nat.primesLE_card_eq_primeCounting] at hge
  have hQpos : (0 : ℝ) < ((∏ q ∈ Nat.primesLE z, q : ℕ) : ℝ) := by
    exact_mod_cast prod_pos fun q hq => (hP q hq).pos
  have hNpos : (0 : ℝ) < ((∏ q ∈ Nat.primesLE z, (q - 1) : ℕ) : ℝ) := by
    exact_mod_cast prod_pos fun q hq => Nat.sub_pos_of_lt (hP q hq).one_lt
  rw [div_le_iff₀ hNpos]
  rw [div_le_div_iff₀ (by positivity) hQpos] at hge
  linarith

/-- At most `π(X)` integers `n < X` make `n - k` prime. -/
theorem card_sub_prime_le (X k : ℕ) :
    #{n ∈ range X | (n - k).Prime} ≤ Nat.primeCounting X := by
  calc #{n ∈ range X | (n - k).Prime} ≤ #{p ∈ range X | p.Prime} := by
        refine card_le_card_of_injOn (fun n => n - k) ?_ ?_
        · intro n hn
          rw [mem_coe, mem_filter, mem_range] at hn
          rw [mem_coe, mem_filter, mem_range]
          exact ⟨lt_of_le_of_lt (Nat.sub_le n k) hn.1, hn.2⟩
        · intro n hn n' hn' h
          rw [mem_coe, mem_filter] at hn hn'
          have h1 := hn.2.two_le
          have h2 := hn'.2.two_le
          simp only at h
          omega
    _ = Nat.primeCounting' X := by
        rw [← Nat.primesBelow_card_eq_primeCounting']; rfl
    _ ≤ Nat.primeCounting X := Nat.monotone_primeCounting' (Nat.le_succ X)

/-- **The finite inequality**, valid for all `X`, `T` and `J ≥ 1`, with `z = 2J + T` and
`Q` the product of the primes up to `z` (the primorial of `z`):
`#{n < X : F n ≤ n + T} ≤ (X + Q)(π z + 1)/(J + 1) + (J + 1) π(X) + 2J + 2`. -/
theorem card_F_le_add_le (T J X : ℕ) (hJ : 1 ≤ J) :
    (#{n ∈ range X | F n ≤ n + T} : ℝ) ≤
      ((X : ℝ) + (∏ q ∈ Nat.primesLE (2 * J + T), q : ℕ)) *
          ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1) +
        (J + 1) * Nat.primeCounting X + (2 * J + 2) := by
  classical
  set z := 2 * J + T with hz
  set P := Nat.primesLE z with hPdef
  have hP : ∀ q ∈ P, q.Prime := fun q hq => Nat.prime_of_mem_primesLE hq
  set I : Finset ℤ := Ico (J : ℤ) (J + (J + 1 : ℕ)) with hI
  set Q : ℕ := ∏ q ∈ P, q with hQ
  set N : ℕ := ∏ q ∈ P, (q - 1) with hN
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast prod_pos fun q hq => (hP q hq).pos
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast prod_pos fun q hq => Nat.sub_pos_of_lt (hP q hq).one_lt
  -- Split `{n < X : F n ≤ n + T}` into three parts.
  have hsplit : (range X).filter (fun n => F n ≤ n + T) ⊆
      ((range X).filter fun n => S P I (res P n) = 0) ∪
        (((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime) ∪
          range (2 * J + 2)) := by
    intro n hn
    rw [mem_filter, mem_range] at hn
    by_cases hsmall : n < 2 * J + 2
    · exact mem_union_right _ (mem_union_right _ (mem_range.mpr hsmall))
    · rcases shift_witness (T := T) hJ (by omega) hn.2 with h | ⟨k, hk, hkp⟩
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr hn.1, h⟩)
      · exact mem_union_right _ (mem_union_left _
          (mem_biUnion.mpr ⟨k, hk, mem_filter.mpr ⟨mem_range.mpr hn.1, hkp⟩⟩))
  have hA : (#((range X).filter fun n => S P I (res P n) = 0) : ℝ) ≤
      ((X : ℝ) + Q) * ((Nat.primeCounting z : ℝ) + 1) / (J + 1) := by
    have h1 := card_res_le P hP X (fun ω => S P I ω = 0)
    have h2 := card_S_eq_zero_le P hP (J : ℤ) (J + 1) (by omega)
    have h3 := prod_div_prod_sub_one_le z
    rw [← hPdef] at h3
    have hdiv : ((X / Q : ℕ) : ℝ) ≤ (X : ℝ) / Q := Nat.cast_div_le
    calc (#((range X).filter fun n => S P I (res P n) = 0) : ℝ)
        ≤ (((X / Q + 1) * #{ω : Omega P | S P I ω = 0} : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (((X / Q : ℕ) : ℝ) + 1) * (#{ω : Omega P | S P I ω = 0} : ℝ) := by push_cast; ring
      _ ≤ ((X : ℝ) / Q + 1) * ((Q : ℝ) ^ 2 / (((J + 1 : ℕ) : ℝ) * N)) := by
          apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
          exact h2
      _ = ((X : ℝ) + Q) * ((Q : ℝ) / N) / (J + 1) := by
          push_cast; field_simp
      _ ≤ ((X : ℝ) + Q) * ((Nat.primeCounting z : ℝ) + 1) / (J + 1) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hB : (#((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime) : ℝ) ≤
      (J + 1) * Nat.primeCounting X := by
    have := card_biUnion_le (s := Icc J (2 * J))
      (t := fun k => (range X).filter fun n => (n - k).Prime)
    have h2 : ∑ k ∈ Icc J (2 * J), #((range X).filter fun n => (n - k).Prime) ≤
        ∑ _k ∈ Icc J (2 * J), Nat.primeCounting X :=
      sum_le_sum fun k _ => card_sub_prime_le X k
    rw [sum_const, Nat.card_Icc, smul_eq_mul] at h2
    have h3 : 2 * J + 1 - J = J + 1 := by omega
    rw [h3] at h2
    exact_mod_cast this.trans h2
  have hC : (#(range (2 * J + 2)) : ℝ) = 2 * J + 2 := by rw [card_range]; push_cast; ring
  calc (#{n ∈ range X | F n ≤ n + T} : ℝ)
      ≤ (#(((range X).filter fun n => S P I (res P n) = 0) ∪
          (((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime) ∪
            range (2 * J + 2))) : ℝ) := by exact_mod_cast card_le_card hsplit
    _ ≤ (#((range X).filter fun n => S P I (res P n) = 0) : ℝ) +
          ((#((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime) : ℝ) +
            #(range (2 * J + 2))) := by
        have h1 := card_union_le ((range X).filter fun n => S P I (res P n) = 0)
          (((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime) ∪
            range (2 * J + 2))
        have h2 := card_union_le
          ((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime)
          (range (2 * J + 2))
        exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
    _ ≤ _ := by rw [hC]; linarith

/-! ### The density statement -/

/-- `π(n) / n → 0`, from Chebyshev's bound `π(x) ≤ log 4 · x / log √x + √x`. -/
theorem tendsto_primeCounting_div :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (√(n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsqrt : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun n : ℕ => Real.log 4 / Real.log (√(n : ℝ)) + 1 / √(n : ℝ))
      atTop (𝓝 0) := by
    have h1 := (tendsto_const_nhds (x := Real.log 4)).div_atTop hlog
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hsqrt
    simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hbound
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hpi := Chebyshev.pi_le_log4_mul_div hn'
  rw [Nat.floor_natCast] at hpi
  have hnpos : (0 : ℝ) < n := by linarith
  have hsq : √(n : ℝ) / n = 1 / √(n : ℝ) := by
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul, Real.mul_self_sqrt hnpos.le]
  calc (Nat.primeCounting n : ℝ) / n ≤ (Real.log 4 * n / Real.log √(n : ℝ) + √(n : ℝ)) / n :=
        div_le_div_of_nonneg_right hpi hnpos.le
    _ = Real.log 4 / Real.log (√(n : ℝ)) + 1 / √(n : ℝ) := by
        rw [add_div, hsq]; congr 1; field_simp

/-- **Erdős Problem 385(ii) for almost all `n`.** For every fixed `T`, the integers `n`
with `F n ≤ n + T` have natural density zero. -/
theorem density_F_le_add (T : ℕ) :
    Tendsto (fun X : ℕ => (#{n ∈ range X | F n ≤ n + T} : ℝ) / X) atTop (𝓝 0) := by
  -- `(π(2J+T) + 1) / (J + 1) → 0` as `J → ∞`.
  have hJlim : Tendsto (fun J : ℕ => ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1))
      atTop (𝓝 0) := by
    have hlin : Tendsto (fun J : ℕ => 2 * J + T) atTop atTop :=
      tendsto_atTop_mono (fun J => show J ≤ 2 * J + T by omega) tendsto_id
    have hpi := tendsto_primeCounting_div.comp hlin
    have hratio : Tendsto (fun J : ℕ => ((2 * J + T : ℕ) : ℝ) / (J + 1)) atTop (𝓝 2) := by
      have : (fun J : ℕ => ((2 * J + T : ℕ) : ℝ) / (J + 1)) =
          fun J : ℕ => 2 + ((T : ℝ) - 2) / ((J : ℝ) + 1) := by
        funext J; push_cast; field_simp; ring
      rw [this]
      simpa using (tendsto_const_nhds (x := (2 : ℝ))).add
        ((tendsto_const_nhds (x := (T : ℝ) - 2)).div_atTop
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
    have hinv : Tendsto (fun J : ℕ => 1 / ((J : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hmain := (hpi.mul hratio).add hinv
    rw [zero_mul, add_zero] at hmain
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with J hJ
    have h1 : ((2 * J + T : ℕ) : ℝ) ≠ 0 := by
      have : 0 < 2 * J + T := by omega
      positivity
    show ((Nat.primeCounting (2 * J + T) : ℝ) / ((2 * J + T : ℕ) : ℝ)) *
        (((2 * J + T : ℕ) : ℝ) / (J + 1)) + 1 / ((J : ℝ) + 1) =
      ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1)
    field_simp
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun X => lt_of_lt_of_le ha (by positivity), ?_⟩
  intro ε hε
  -- Choose `J` with `(π(2J+T) + 1)/(J + 1) < ε / 2`.
  obtain ⟨J, hJ1, hJ⟩ : ∃ J : ℕ, 1 ≤ J ∧
      ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1) < ε / 2 := by
    have := (hJlim.eventually (gt_mem_nhds (half_pos hε))).and (eventually_ge_atTop 1)
    obtain ⟨J, hJ⟩ := this.exists
    exact ⟨J, hJ.2, hJ.1⟩
  set c : ℝ := ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1) with hc
  set Q : ℝ := ((∏ q ∈ Nat.primesLE (2 * J + T), q : ℕ) : ℝ) with hQ
  -- The upper bound divided by `X` tends to `c < ε / 2`.
  have hu : Tendsto (fun X : ℕ => (1 + Q / X) * c + (J + 1) * ((Nat.primeCounting X : ℝ) / X) +
      (2 * J + 2) / (X : ℝ)) atTop (𝓝 ((1 + 0) * c + (J + 1) * 0 + 0)) := by
    have hX : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    refine (((tendsto_const_nhds.add ((tendsto_const_nhds (x := Q)).div_atTop hX)).mul
      tendsto_const_nhds).add (tendsto_const_nhds.mul tendsto_primeCounting_div)).add
      ((tendsto_const_nhds (x := (2 * (J : ℝ) + 2))).div_atTop hX)
  simp only [add_zero, one_mul, mul_zero] at hu
  filter_upwards [hu.eventually (gt_mem_nhds (by linarith : c < ε)), eventually_ge_atTop 1]
    with X hXu hX1
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hbound := card_F_le_add_le T J X hJ1
  calc (#{n ∈ range X | F n ≤ n + T} : ℝ) / X
      ≤ (((X : ℝ) + Q) * ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1) +
          (J + 1) * Nat.primeCounting X + (2 * J + 2)) / X :=
        div_le_div_of_nonneg_right hbound hXpos.le
    _ = (1 + Q / X) * c + (J + 1) * ((Nat.primeCounting X : ℝ) / X) + (2 * J + 2) / (X : ℝ) := by
        rw [hc]; field_simp
    _ < ε := hXu

/-! ### Thresholds growing with `X` -/

/-- Chebyshev's bound in the form `π(X) ≤ 2 log 4 · X / log X + √X`. -/
theorem primeCounting_le_aux {X : ℕ} (hX : 2 ≤ X) :
    (Nat.primeCounting X : ℝ) ≤ 2 * Real.log 4 * X / Real.log X + √(X : ℝ) := by
  have hX' : (1 : ℝ) < X := by exact_mod_cast hX
  have h := Chebyshev.pi_le_log4_mul_div hX'
  rw [Nat.floor_natCast, Real.log_sqrt (by positivity)] at h
  have hlogpos : 0 < Real.log X := Real.log_pos hX'
  calc (Nat.primeCounting X : ℝ) ≤ Real.log 4 * X / (Real.log X / 2) + √(X : ℝ) := h
    _ = 2 * Real.log 4 * X / Real.log X + √(X : ℝ) := by field_simp

/-- `π(z) ≤ z + 1`, a trivial bound. -/
theorem primeCounting_le_succ (z : ℕ) : Nat.primeCounting z ≤ z + 1 := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range]
  exact (card_filter_le _ _).trans (card_range _).le

/-- `4 ^ n ≤ √X` as soon as `6 n log 4 ≤ log X`. -/
theorem four_pow_le_sqrt {n X : ℕ} (hX : 1 ≤ X) (h : 6 * n * Real.log 4 ≤ Real.log X) :
    (4 : ℝ) ^ n ≤ √(X : ℝ) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  rw [Real.le_sqrt (by positivity) hXpos.le, ← pow_mul]
  have h4 : (4 : ℝ) ^ (n * 2) = Real.exp (Real.log 4 * (n * 2 : ℕ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  rw [h4, ← Real.exp_log hXpos]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]

/-- **Thresholds growing slower than `log X`.** If `T(X) / log X → 0`, then the `n < X` with
`F n ≤ n + T(X)` have density zero. In particular `F(n) - n ≥ log n / ω(n)` for almost all
`n`, for any `ω → ∞`. -/
theorem density_F_le_add_of_tendsto (T : ℕ → ℕ)
    (hT : Tendsto (fun X : ℕ => (T X : ℝ) / Real.log X) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ => (#{n ∈ range X | F n ≤ n + T X} : ℝ) / X) atTop (𝓝 0) := by
  -- The auxiliary parameter `J(X) = T(X) + ⌊√(log X)⌋ + 1` tends to infinity, but slower
  -- than `log X`.
  set s : ℕ → ℕ := fun X => ⌊√(Real.log X)⌋₊ with hsdef
  set J : ℕ → ℕ := fun X => T X + s X + 1 with hJdef
  set z : ℕ → ℕ := fun X => 2 * J X + T X with hzdef
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun X : ℕ => √(Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hs : Tendsto s atTop atTop := tendsto_nat_floor_atTop.comp hsq
  have hJ : Tendsto J atTop atTop :=
    tendsto_atTop_mono (fun X => show s X ≤ T X + s X + 1 by omega) hs
  have hz : Tendsto z atTop atTop :=
    tendsto_atTop_mono (fun X => show J X ≤ 2 * J X + T X by omega) hJ
  have hJlog : Tendsto (fun X : ℕ => ((J X : ℝ) + 1) / Real.log X) atTop (𝓝 0) := by
    have hs' : Tendsto (fun X : ℕ => (s X : ℝ) / Real.log X) atTop (𝓝 0) := by
      have hinv : Tendsto (fun X : ℕ => 1 / √(Real.log X)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hsq
      refine squeeze_zero' (Eventually.of_forall fun X => by positivity) ?_ hinv
      filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with X hX
      have hfl : (s X : ℝ) ≤ √(Real.log X) := Nat.floor_le (Real.sqrt_nonneg _)
      calc (s X : ℝ) / Real.log X ≤ √(Real.log X) / Real.log X :=
            div_le_div_of_nonneg_right hfl hX.le
        _ = 1 / √(Real.log X) := by
            rw [div_eq_div_iff hX.ne' (Real.sqrt_pos.mpr hX).ne', one_mul,
              Real.mul_self_sqrt hX.le]
    have h2 : Tendsto (fun X : ℕ => (2 : ℝ) / Real.log X) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have hsum := (hT.add hs').add h2
    rw [add_zero, add_zero] at hsum
    refine hsum.congr' (Eventually.of_forall fun X => ?_)
    simp only [hJdef]
    push_cast
    ring
  -- The bounding sequence and its limit.
  set b : ℕ → ℝ := fun X =>
    3 * ((Nat.primeCounting (z X) : ℝ) / z X) + 1 / ((J X : ℝ) + 1) + 6 / Real.log X +
      (2 * Real.log 4 + 4) * (((J X : ℝ) + 1) / Real.log X) with hbdef
  have hb : Tendsto b atTop (𝓝 0) := by
    have h1 := (tendsto_primeCounting_div.comp hz).const_mul 3
    have h2 : Tendsto (fun X : ℕ => 1 / ((J X : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hJ))
    have h3 : Tendsto (fun X : ℕ => (6 : ℝ) / Real.log X) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have h4 := hJlog.const_mul (2 * Real.log 4 + 4)
    have hsum := ((h1.add h2).add h3).add h4
    simp only [mul_zero, add_zero] at hsum
    exact hsum
  refine squeeze_zero' (Eventually.of_forall fun X => by positivity) ?_ hb
  have hsmall : ∀ᶠ X : ℕ in atTop, ((J X : ℝ) + 1) / Real.log X < 1 / (18 * Real.log 4) :=
    hJlog.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 3, hz.eventually (eventually_ge_atTop 1)]
    with X hXs hX3 hz1
  -- Basic facts at this `X`.
  have hX1 : 1 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hlogpos : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hJpos : (0 : ℝ) < (J X : ℝ) + 1 := by positivity
  have hTJ : T X ≤ J X := by simp only [hJdef]; omega
  have hzJ : (z X : ℝ) ≤ 3 * ((J X : ℝ) + 1) := by
    have : z X ≤ 3 * J X := by simp only [hzdef]; omega
    have : (z X : ℝ) ≤ 3 * J X := by exact_mod_cast this
    linarith
  have hzpos : (0 : ℝ) < z X := by exact_mod_cast hz1
  have hJ6 : 6 * (z X : ℝ) * Real.log 4 ≤ Real.log X := by
    have h := hXs
    rw [div_lt_div_iff₀ hlogpos (by positivity), one_mul] at h
    have hz3 : (z X : ℝ) ≤ 3 * J X := by
      have : z X ≤ 3 * J X := by simp only [hzdef]; omega
      exact_mod_cast this
    nlinarith [mul_le_mul_of_nonneg_right hz3 hlog4.le]
  -- `√X ≤ X` and `log X ≤ 2 √X`.
  have hsqrtX : 0 < √(X : ℝ) := Real.sqrt_pos.mpr hXpos
  have hlogsqrt : Real.log X ≤ 2 * √(X : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hsqrtX
    rw [Real.log_sqrt hXpos.le] at h
    linarith
  have hlogX : Real.log X ≤ X := Real.log_le_self hXpos.le
  -- The finite inequality.
  have hmain := card_F_le_add_le (T X) (J X) X (by simp only [hJdef]; omega)
  have hQ : ((∏ q ∈ Nat.primesLE (2 * J X + T X), q : ℕ) : ℝ) ≤ √(X : ℝ) := by
    have h1 : (∏ q ∈ Nat.primesLE (2 * J X + T X), q) ≤ 4 ^ (2 * J X + T X) :=
      primorial_le_four_pow _
    calc ((∏ q ∈ Nat.primesLE (2 * J X + T X), q : ℕ) : ℝ) ≤ (4 : ℝ) ^ (2 * J X + T X) := by
          exact_mod_cast h1
      _ ≤ √(X : ℝ) := four_pow_le_sqrt hX1 (by push_cast; simpa [hzdef] using hJ6)
  have hpiz : (Nat.primeCounting (z X) : ℝ) + 1 ≤ 3 * ((J X : ℝ) + 1) := by
    have := primeCounting_le_succ (z X)
    have : (Nat.primeCounting (z X) : ℝ) ≤ z X + 1 := by exact_mod_cast this
    have : (z X : ℝ) ≤ 3 * J X := by
      have : z X ≤ 3 * J X := by simp only [hzdef]; omega
      exact_mod_cast this
    linarith
  have hpiX := primeCounting_le_aux (show 2 ≤ X by omega)
  -- Bound each term of `card / X`.
  set Q : ℝ := ((∏ q ∈ Nat.primesLE (2 * J X + T X), q : ℕ) : ℝ) with hQdef
  set c : ℝ := ((Nat.primeCounting (z X) : ℝ) + 1) / ((J X : ℝ) + 1) with hcdef
  have hc1 : c ≤ 3 * ((Nat.primeCounting (z X) : ℝ) / z X) + 1 / ((J X : ℝ) + 1) := by
    rw [hcdef, add_div]
    have : (Nat.primeCounting (z X) : ℝ) / ((J X : ℝ) + 1) ≤
        3 * ((Nat.primeCounting (z X) : ℝ) / z X) := by
      rw [div_le_iff₀ hJpos, mul_comm 3, mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hzpos]
      have : (0 : ℝ) ≤ Nat.primeCounting (z X) := by positivity
      nlinarith
    linarith
  have hc3 : c ≤ 3 := by rw [hcdef, div_le_iff₀ hJpos]; linarith
  have hterm2 : Q / X * c ≤ 6 / Real.log X := by
    have hQX : Q / X ≤ 2 / Real.log X := by
      rw [div_le_div_iff₀ hXpos hlogpos]
      calc Q * Real.log X ≤ √(X : ℝ) * (2 * √(X : ℝ)) :=
            mul_le_mul hQ hlogsqrt hlogpos.le hsqrtX.le
        _ = 2 * X := by rw [mul_left_comm, Real.mul_self_sqrt hXpos.le]
    calc Q / X * c ≤ 2 / Real.log X * 3 :=
          mul_le_mul hQX hc3 (by positivity) (by positivity)
      _ = 6 / Real.log X := by ring
  have hterm3 : ((J X : ℝ) + 1) * Nat.primeCounting X / X ≤
      (2 * Real.log 4 + 2) * (((J X : ℝ) + 1) / Real.log X) := by
    rw [mul_div_assoc]
    have : (Nat.primeCounting X : ℝ) / X ≤ (2 * Real.log 4 + 2) / Real.log X := by
      rw [div_le_div_iff₀ hXpos hlogpos]
      have h1 : 2 * Real.log 4 * X / Real.log X * Real.log X = 2 * Real.log 4 * X := by
        field_simp
      have h2 : √(X : ℝ) * Real.log X ≤ 2 * X := by
        calc √(X : ℝ) * Real.log X ≤ √(X : ℝ) * (2 * √(X : ℝ)) :=
              mul_le_mul_of_nonneg_left hlogsqrt hsqrtX.le
          _ = 2 * X := by rw [mul_left_comm, Real.mul_self_sqrt hXpos.le]
      nlinarith [mul_le_mul_of_nonneg_right hpiX hlogpos.le]
    calc ((J X : ℝ) + 1) * ((Nat.primeCounting X : ℝ) / X)
        ≤ ((J X : ℝ) + 1) * ((2 * Real.log 4 + 2) / Real.log X) :=
          mul_le_mul_of_nonneg_left this hJpos.le
      _ = (2 * Real.log 4 + 2) * (((J X : ℝ) + 1) / Real.log X) := by ring
  have hterm4 : (2 * (J X : ℝ) + 2) / X ≤ 2 * (((J X : ℝ) + 1) / Real.log X) := by
    rw [div_le_iff₀ hXpos]
    have : ((J X : ℝ) + 1) / Real.log X * X ≥ (J X : ℝ) + 1 := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hlogpos]
      exact mul_le_mul_of_nonneg_left hlogX hJpos.le
    linarith
  calc (#{n ∈ range X | F n ≤ n + T X} : ℝ) / X
      ≤ (((X : ℝ) + Q) * ((Nat.primeCounting (z X) : ℝ) + 1) / ((J X : ℝ) + 1) +
          ((J X : ℝ) + 1) * Nat.primeCounting X + (2 * (J X : ℝ) + 2)) / X :=
        div_le_div_of_nonneg_right hmain hXpos.le
    _ = c + Q / X * c + ((J X : ℝ) + 1) * Nat.primeCounting X / X +
          (2 * (J X : ℝ) + 2) / X := by
        rw [hcdef]; field_simp
    _ ≤ (3 * ((Nat.primeCounting (z X) : ℝ) / z X) + 1 / ((J X : ℝ) + 1)) + 6 / Real.log X +
          (2 * Real.log 4 + 2) * (((J X : ℝ) + 1) / Real.log X) +
          2 * (((J X : ℝ) + 1) / Real.log X) := by linarith
    _ = b X := by rw [hbdef]; ring

end Erdos430

#print axioms Erdos430.density_F_le_add_of_tendsto
#print axioms Erdos430.card_S_eq_zero_le
#print axioms Erdos430.card_F_le_add_le
#print axioms Erdos430.density_F_le_add
