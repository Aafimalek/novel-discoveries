import EulerNumbering

/-!
# Semantics of the support at-most-one sequential counter

This is the three-clause-family Sinz-style at-most-one counter observed in
the actual PySAT prefix. Its k−1 auxiliary bits may be assigned by prefix
existence. Exact placement cardinality, later degree variables and cuts are
not modeled here.
-/

namespace LatinGap.PairEncoding

/-- Clause semantics for k inputs and k−1 sequential counter states. -/
def SequentialAMO (k : Nat) (x s : Nat → Bool) : Prop :=
  (∀ i, i + 1 < k → x i = true → s i = true) ∧
  (∀ i, i + 2 < k → s i = true → s (i + 1) = true) ∧
  (∀ i, i + 1 < k → x (i + 1) = true → s i = false)

/-- Pairwise exclusion for the list of input bits. -/
def PairwiseAMO (k : Nat) (x : Nat → Bool) : Prop :=
  ∀ i j, i < j → j < k → x i = true → x j = false

private theorem state_propagates {k : Nat} {s : Nat → Bool}
    (hs : ∀ i, i + 2 < k → s i = true → s (i + 1) = true)
    (lo hi : Nat) (h : lo ≤ hi) (hb : hi + 1 < k) (ht : s lo = true) :
    s hi = true := by
  induction hi with
  | zero => rwa [show lo = 0 by omega] at ht
  | succ j ih =>
    by_cases h' : lo = j + 1
    · simpa [h'] using ht
    · exact hs j (by omega) (ih (by omega) (by omega))

/-- The physical auxiliary states give exactly existential at-most-one,
with no additional restriction on the input bits. -/
theorem sequentialAMO_iff (k : Nat) (x : Nat → Bool) :
    (∃ s, SequentialAMO k x s) ↔ PairwiseAMO k x := by
  constructor
  · rintro ⟨s, hstart, hmono, hstop⟩ i j hij hj hxi
    have hi : s i = true := hstart i (by omega) hxi
    have h' : s (j - 1) = true :=
      state_propagates hmono i (j - 1) (by omega) (by omega) hi
    cases hval : x j with
    | false => rfl
    | true =>
      have he : j - 1 + 1 = j := by omega
      have hf := hstop (j - 1) (by omega) (by simpa only [he] using hval)
      rw [hf] at h'
      contradiction
  · classical
    intro h
    let s (i : Nat) : Bool := decide (∃ u, u ≤ i ∧ x u = true)
    refine ⟨s, ?_, ?_, ?_⟩
    · intro i _ hi
      exact decide_eq_true ⟨i, le_rfl, hi⟩
    · intro i _ hi
      obtain ⟨u, hu, ht⟩ := of_decide_eq_true hi
      exact decide_eq_true ⟨u, by omega, ht⟩
    · intro i hb hi
      apply decide_eq_false
      rintro ⟨u, hu, ht⟩
      have hf := h u (i+1) (by omega) hb ht
      rw [hf] at hi
      contradiction

end LatinGap.PairEncoding

#print axioms LatinGap.PairEncoding.sequentialAMO_iff
