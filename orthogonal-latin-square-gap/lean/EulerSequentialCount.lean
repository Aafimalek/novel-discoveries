import EulerSequentialAMO

/-!
# Exact cardinality using the PySAT sequential-counter grid

This is the rectangular, diagonally indexed form of the usual sequential
counter. An input of length `m + k` is constrained to have at most `k`
ones. Physical state `s r j` is the one-sided assertion that the first
`r + j + 1` bits contain at least `j + 1` ones, where `r < m` and `j < k`.
-/

namespace LatinGap.PairEncoding

def prefixOnes (x : Nat → Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => prefixOnes x i + if x i then 1 else 0

theorem prefixOnes_le (x : Nat → Bool) (i : Nat) : prefixOnes x i ≤ i := by
  induction i with
  | zero => simp [prefixOnes]
  | succ i h =>
    cases hx : x i <;> simp [prefixOnes, hx] <;> omega

/-- Implications of all physical clause families of the truncated grid. -/
def SequentialBound (m k : Nat) (x : Nat → Bool) (s : Nat → Nat → Bool) : Prop :=
  (∀ r, r < m → x r = true → s r 0 = true) ∧
  (∀ r j, r + 1 < m → j < k → s r j = true → s (r + 1) j = true) ∧
  (∀ r j, r < m → j + 1 < k → s r j = true → x (r + j + 1) = true →
      s r (j + 1) = true) ∧
  (∀ r, r < m → s r (k - 1) = true → x (r + k) = false)

private theorem every_required_state {m k : Nat} {x : Nat → Bool} {s : Nat → Nat → Bool}
    (h : SequentialBound m k x s) (r j : Nat) (hr : r < m) (hj : j < k)
    (hcount : j + 1 ≤ prefixOnes x (r + j + 1)) : s r j = true := by
  rcases h with ⟨hs, hh, hd, hf⟩
  have derive : ∀ t, ∀ r j, r + j = t → r < m → j < k →
      j + 1 ≤ prefixOnes x (r + j + 1) → s r j = true := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro r j hsum hr hj hc
      rw [prefixOnes] at hc
      by_cases hprev : j + 1 ≤ prefixOnes x (r + j)
      · have rpos : 0 < r := by have hb := prefixOnes_le x (r+j); omega
        have hh' := hh (r - 1) j (by omega) hj
        rw [show r - 1 + 1 = r by omega] at hh'
        apply hh'
        apply ih (r - 1 + j) (by omega) (r - 1) j rfl (by omega) hj
        rwa [show r - 1 + j + 1 = r + j by omega]
      · have hx : x (r+j) = true := by
          cases he : x (r+j) <;> simp [he] at hc ⊢
          omega
        by_cases hj0 : j = 0
        · subst j
          exact hs r hr (by simpa using hx)
        · have hb : j ≤ prefixOnes x (r+j) := by simp [hx] at hc; omega
          have hd' := hd r (j - 1) hr (by omega)
          have hp := ih (r + (j - 1)) (by omega) r (j-1) rfl hr (by omega) (by
            rw [show r + (j - 1) + 1 = r + j by omega]
            omega)
          rw [show j - 1 + 1 = j by omega, show r + (j - 1) + 1 = r + j by omega] at hd'
          exact hd' hp hx
  exact derive (r+j) r j rfl hr hj hcount

/-- The rectangular counter has a satisfying assignment exactly for
inputs with at most the given number of selected entries. -/
theorem sequentialBound_iff (m k : Nat) (hk : 0 < k) (x : Nat → Bool) :
    (∃ s, SequentialBound m k x s) ↔ prefixOnes x (m+k) ≤ k := by
  constructor
  · rintro ⟨s, h⟩
    have advance : ∀ i, i ≤ m+k → prefixOnes x i ≤ k := by
      intro i
      induction i with
      | zero => simp [prefixOnes]
      | succ i ih =>
        intro hi
        have hprior := ih (by omega)
        rw [prefixOnes]
        cases hx : x i with
        | false => simpa [hx] using hprior
        | true =>
          simp
          by_contra! hfail
          have heq : prefixOnes x i = k := by omega
          have hki : k ≤ i := by have := prefixOnes_le x i; omega
          have hS : s (i-k) (k-1) = true :=
            every_required_state h (i-k) (k-1) (by omega) (by omega) (by
              rw [show i - k + (k - 1) + 1 = i by omega]
              omega)
          have hF := h.2.2.2 (i-k) (by omega) hS
          rw [show i - k + k = i by omega, hx] at hF
          contradiction
    exact advance (m+k) le_rfl
  · intro hn
    let s : Nat → Nat → Bool :=
      fun r j => decide (j + 1 ≤ prefixOnes x (r+j+1))
    have mono : ∀ i j, i ≤ j → prefixOnes x i ≤ prefixOnes x j := by
      intro i j h
      induction j with
      | zero =>
        have hi : i = 0 := by omega
        rw [hi]
      | succ j ih =>
        by_cases h' : i = j+1
        · subst i; exact le_rfl
        · have h'' := ih (by omega)
          rw [prefixOnes]
          omega
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · intro r _ hx
      apply decide_eq_true
      simp [prefixOnes, hx]
    · intro r j _ _ hs
      apply decide_eq_true
      exact (of_decide_eq_true hs).trans (mono _ _ (by omega))
    · intro r j _ _ hs hx
      have hh : j+1 ≤ prefixOnes x (r+j+1) := of_decide_eq_true hs
      apply decide_eq_true
      rw [show r+(j+1)+1 = (r+j+1)+1 by omega, prefixOnes, hx]
      simp
      omega
    · intro r hr hs
      have hh : k-1+1 ≤ prefixOnes x (r+(k-1)+1) := of_decide_eq_true hs
      rw [show r+(k-1)+1 = r+k by omega] at hh
      cases hx : x (r+k) with
      | false => rfl
      | true =>
        have hm := mono (r+k+1) (m+k) (by omega)
        rw [prefixOnes, hx] at hm
        simp at hm
        omega

theorem prefixOnes_complement (x : Nat → Bool) (n : Nat) :
    prefixOnes x n + prefixOnes (fun i => ! x i) n = n := by
  induction n with
  | zero => simp [prefixOnes]
  | succ n ih =>
    cases hx : x n <;> simp [prefixOnes, hx] <;> omega

/-- The two independent sequential counters encode exact cardinality. -/
theorem sequentialExact_iff (m k : Nat) (hm : 0 < m) (hk : 0 < k) (x : Nat → Bool) :
    (∃ z s, SequentialBound k m (fun i => ! x i) z ∧ SequentialBound m k x s)
      ↔ prefixOnes x (m+k) = k := by
  have hz := sequentialBound_iff k m hm (fun i => ! x i)
  have hs := sequentialBound_iff m k hk x
  have hc := prefixOnes_complement x (m+k)
  constructor
  · rintro ⟨z, s, h₁, h₂⟩
    have h₁' := hz.mp ⟨z, h₁⟩
    have h₂' := hs.mp ⟨s, h₂⟩
    rw [Nat.add_comm k m] at h₁'
    omega
  · intro h
    have hz' : prefixOnes (fun i => ! x i) (k+m) ≤ m := by
      rw [Nat.add_comm k m]
      omega
    have hs' : prefixOnes x (m+k) ≤ k := by omega
    obtain ⟨z, h₁⟩ := hz.mpr hz'
    obtain ⟨s, h₂⟩ := hs.mpr hs'
    exact ⟨z, s, h₁, h₂⟩

/-- The two physical blocks following the support counters: at most 19
zeros and at most 17 ones among the 36 bits of the first projection. -/
theorem projection_seventeen_counter_iff (x : Nat → Bool) :
    (∃ z s, SequentialBound 17 19 (fun i => ! x i) z ∧ SequentialBound 19 17 x s)
      ↔ prefixOnes x 36 = 17 :=
  sequentialExact_iff 19 17 (by decide) (by decide) x

/-- The later two-block counter in each coordinate constrains its 24
selected unary threshold bits to contain exactly five ones. -/
theorem degree_excess_five_counter_iff (x : Nat → Bool) :
    (∃ z s, SequentialBound 5 19 (fun i => ! x i) z ∧ SequentialBound 19 5 x s)
      ↔ prefixOnes x 24 = 5 :=
  sequentialExact_iff 19 5 (by decide) (by decide) x

end LatinGap.PairEncoding

#print axioms LatinGap.PairEncoding.sequentialBound_iff
#print axioms LatinGap.PairEncoding.projection_seventeen_counter_iff
#print axioms LatinGap.PairEncoding.degree_excess_five_counter_iff
