import Mathlib.Basic.Real.Basic

/-! Local arithmetic for the dense signed-rank interval.
This draft does not encode the subset-sum geometry establishing the hypotheses. -/

namespace NineSeparatedSubsetSums

theorem exact_gap_displacement
    {m r : ℕ} {e a b δ : ℝ}
    (hab : a ≤ b) (ha : -1 ≤ a) (hb : b ≤ δ) (hδ : δ < 1)
    (hme : (m : ℝ) ≤ e) (hem : e < (m : ℝ) + 1)
    (heq : 2 * (r : ℝ) + b - a = 2 * e) :
    r = m := by
  have hd0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hd2 : b - a < 2 := calc
    b - a ≤ δ - (-1 : ℝ) := sub_le_sub hb ha
    _ = δ + 1 := sub_neg_eq_add _ _
    _ < (1 : ℝ) + 1 := add_lt_add_left hδ 1
    _ = 2 := one_add_one_eq_two
  have heq' : 2 * (r : ℝ) + (b - a) = 2 * e := by
    rw [← add_sub_assoc, heq]
  have h2 : (0 : ℝ) < 2 := zero_lt_two
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hh : r + 1 ≤ m := Nat.succ_le_of_lt hlt
    have hh₁ : ((r + 1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hh
    have hh' : (r : ℝ) + 1 ≤ (m : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hh₁
    have hbad : (2 : ℝ) * e < 2 * (m : ℝ) := calc
      2 * e = 2 * (r : ℝ) + (b - a) := heq'.symm
      _ < 2 * (r : ℝ) + 2 := add_lt_add_right hd2 _
      _ = 2 * ((r : ℝ) + 1) := by rw [mul_add, mul_one]
      _ ≤ 2 * (m : ℝ) := mul_le_mul_of_nonneg_left hh' h2.le
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left hme h2.le)) hbad
  · have hh : m + 1 ≤ r := Nat.succ_le_of_lt hgt
    have hh₁ : ((m + 1 : ℕ) : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr hh
    have hh' : (m : ℝ) + 1 ≤ (r : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hh₁
    have hbad : (2 : ℝ) * e < 2 * e := calc
      2 * e < 2 * ((m : ℝ) + 1) := mul_lt_mul_of_pos_left hem h2
      _ ≤ 2 * (r : ℝ) := mul_le_mul_of_nonneg_left hh' h2.le
      _ ≤ 2 * (r : ℝ) + (b - a) := le_add_of_nonneg_right hd0
      _ = 2 * e := heq'
    exact (lt_irrefl _ hbad)

inductive TopSigns
  | ppp | ppm | pmp | pmm | mpp | mpm | mmp | mmm

/-- The exact signed-rank requirements for the normalized `3 ≤ e < 4` band
cannot be met. The real subset-sum reduction must still provide them. -/
theorem wide_three_top_collision
    (T : ℕ → TopSigns) (v50 v53 v60 v63 : Bool)
    (h49 : T 49 = if v50 then .ppm else .mpm)
    (h63 : T 63 = if v63 then .pmp else .mmp)
    (h53 : if v53 then T 56 = TopSigns.mpp else T 49 = TopSigns.pmm)
    (h60 : if v60 then T 63 = TopSigns.mpp else T 56 = TopSigns.pmm) :
    False := by
  cases v50 <;> cases v53 <;> cases v60 <;> cases v63 <;> simp_all

#print axioms exact_gap_displacement
#print axioms wide_three_top_collision

end NineSeparatedSubsetSums
