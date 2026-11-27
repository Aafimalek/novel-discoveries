import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace FranklHeightThreeArithmetic

/-- Simplify the basic counting bound when the ground has (i+k+L) points
and the trace ground has (i+k-2) points. -/
theorem tail_le_choose_of_basic
    {n m i k L : ℕ} (hn : n = i + k + L) (hm : m = i + k - 2)
    (hk : 2 ≤ k) (hbasic : n - 1 ≤ 1 + m + m.choose 2) :
    L ≤ m.choose 2 := by
  omega

/-- The case split in the strengthened counting bound has a tail-only form. -/
theorem strengthened_tail_bounds
    {n m i k L : ℕ} (hn : n = i + k + L) (hm : m = i + k - 2)
    (hk : 2 ≤ k) (hmpos : 1 ≤ m)
    (h : n - 1 ≤ 1 + (m - 1) + (m - 1).choose 2 ∨
      n - 1 + (k - 2).choose 2 ≤ 1 + m + m.choose 2) :
    L + 1 ≤ (m - 1).choose 2 ∨ L + (k - 2).choose 2 ≤ m.choose 2 := by
  rcases h with h | h
  · left
    omega
  · right
    omega

/-- If there are no isolated points ((i=0)), the multiplicity term rules
out the second branch; only the stronger predecessor-size bound remains. -/
theorem tail_le_predecessor_choose_of_no_isolates
    {n m k L : ℕ} (hn : n = k + L) (hm : m = k - 2)
    (hk : 2 ≤ k) (hmpos : 1 ≤ m) (hL : k ≤ L)
    (h : n - 1 ≤ 1 + (m - 1) + (m - 1).choose 2 ∨
      n - 1 + (k - 2).choose 2 ≤ 1 + m + m.choose 2) :
    L + 1 ≤ (k - 3).choose 2 := by
  have hsplit := strengthened_tail_bounds (i := 0)
    (by simpa using hn) (by simpa using hm) hk hmpos h
  have hm' : m - 1 = k - 3 := by omega
  rcases hsplit with hleft | hright
  · rwa [hm'] at hleft
  · rw [hm] at hright
    omega

/-- In the absence of isolated points, the smaller side has size at least 8;
at size 8 the larger side has size 8 or 9. -/
theorem no_isolates_side_bounds
    {n m k L : ℕ} (hn : n = k + L) (hm : m = k - 2)
    (hk : 2 ≤ k) (hmpos : 1 ≤ m) (hL : k ≤ L)
    (h : n - 1 ≤ 1 + (m - 1) + (m - 1).choose 2 ∨
      n - 1 + (k - 2).choose 2 ≤ 1 + m + m.choose 2) :
    8 ≤ k ∧ (k = 8 → 8 ≤ L ∧ L ≤ 9) := by
  have ht := tail_le_predecessor_choose_of_no_isolates hn hm hk hmpos hL h
  constructor
  · by_contra! hlt
    interval_cases k <;> norm_num [Nat.choose_two_right] at ht <;> omega
  · rintro rfl
    norm_num [Nat.choose_two_right] at ht
    omega

/-- Quantify the slack below the basic binomial bound. The first branch saves
(m) slots and the second branch saves (inom{k-2}{2}) slots. -/
theorem tail_add_min_le_choose_of_strengthened
    {n m i k L : ℕ} (hn : n = i + k + L) (hm : m = i + k - 2)
    (hk : 2 ≤ k) (hmpos : 1 ≤ m)
    (h : n - 1 ≤ 1 + (m - 1) + (m - 1).choose 2 ∨
      n - 1 + (k - 2).choose 2 ≤ 1 + m + m.choose 2) :
    L + min m ((k - 2).choose 2) ≤ m.choose 2 := by
  rcases strengthened_tail_bounds hn hm hk hmpos h with hleft | hright
  · have hpascal := Nat.choose_succ_succ' (m - 1) 1
    have heq : m - 1 + 1 = m := by omega
    rw [heq, Nat.choose_one_right] at hpascal
    change m.choose 2 = (m - 1) + (m - 1).choose 2 at hpascal
    have hmin := min_le_left m ((k - 2).choose 2)
    omega
  · have hmin := min_le_right m ((k - 2).choose 2)
    omega

/-- For smaller side at least 4, the strengthened counting bound leaves a
strict gap below the basic binomial upper bound. -/
theorem tail_lt_choose_of_strengthened
    {n m i k L : ℕ} (hn : n = i + k + L) (hm : m = i + k - 2)
    (hk : 4 ≤ k)
    (h : n - 1 ≤ 1 + (m - 1) + (m - 1).choose 2 ∨
      n - 1 + (k - 2).choose 2 ≤ 1 + m + m.choose 2) :
    L < m.choose 2 := by
  rcases strengthened_tail_bounds hn hm (by omega) (by omega) h with hleft | hright
  · have hmono : (m - 1).choose 2 ≤ m.choose 2 := Nat.choose_mono 2 (Nat.sub_le m 1)
    omega
  · have hpos : 0 < (k - 2).choose 2 := Nat.choose_pos (by omega)
    omega

theorem basic_strict_of_strengthened
    {n m i k L : ℕ} (hn : n = i + k + L) (hm : m = i + k - 2)
    (hk : 4 ≤ k)
    (h : n - 1 ≤ 1 + (m - 1) + (m - 1).choose 2 ∨
      n - 1 + (k - 2).choose 2 ≤ 1 + m + m.choose 2) :
    n - 1 < 1 + m + m.choose 2 := by
  have ht := tail_lt_choose_of_strengthened hn hm hk h
  omega

#print axioms tail_le_choose_of_basic
#print axioms no_isolates_side_bounds
#print axioms basic_strict_of_strengthened
#print axioms tail_add_min_le_choose_of_strengthened

end FranklHeightThreeArithmetic
