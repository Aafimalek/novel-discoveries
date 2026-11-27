import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace NineSeparatedSubsetSums

def liftScore (M s : ℝ) (flag : Bool) : ℝ := s + if flag then M else 0

/-- A first-eight-coordinate sum is the projection of a score in the
width-M critical interval exactly when it is in the width-2M slab. -/
theorem lift_exists_iff_in_slab (c M s : ℝ) (hM : 0 ≤ M) :
    (∃ b : Bool, c ≤ liftScore M s b ∧ liftScore M s b ≤ c + M) ↔
      c - M ≤ s ∧ s ≤ c + M := by
  constructor
  · rintro ⟨b, h, h'⟩
    cases b <;> simp only [liftScore, Bool.false_eq_true, if_false, if_true, add_zero] at h h'
    all_goals exact ⟨by linarith, by linarith⟩
  · rintro ⟨h, h'⟩
    by_cases hc : c ≤ s
    · exact ⟨false, by simpa [liftScore] using hc, by simpa [liftScore] using h'⟩
    · exact ⟨true, by simp [liftScore]; linarith, by simp [liftScore]; linarith⟩

theorem two_lifts_only_at_endpoint (c M s : ℝ)
    (h : c ≤ liftScore M s false) (h' : liftScore M s true ≤ c + M) :
    s = c := by
  simp [liftScore] at h h'
  linarith

/-- Against a direction increase x, a lifted critical-interval edge can
have unsigned length x or M-x. The third formal option M+x is too long. -/
theorem projected_edge_length (c M s x : ℝ) (hx : 0 < x) (hbound : x ≤ M)
    (a b : Bool)
    (ha : c ≤ liftScore M s a ∧ liftScore M s a ≤ c + M)
    (hb : c ≤ liftScore M (s + x) b ∧ liftScore M (s + x) b ≤ c + M) :
    |liftScore M (s + x) b - liftScore M s a| = x ∨
    |liftScore M (s + x) b - liftScore M s a| = M - x := by
  cases a <;> cases b
  · left
    simp only [liftScore, Bool.false_eq_true, if_false, add_zero]
    rw [show s + x - s = x by linarith, abs_of_nonneg hx.le]
  · exfalso
    simp [liftScore] at ha hb
    linarith [ha.1, hb.2]
  · right
    simp only [liftScore, Bool.false_eq_true, if_false, if_true, add_zero]
    rw [show s + x - (s + M) = x - M by linarith, abs_of_nonpos (by linarith : x - M ≤ 0)]
    linarith
  · left
    simp only [liftScore, if_true]
    rw [show s + x + M - (s + M) = x by linarith, abs_of_nonneg hx.le]

#print axioms lift_exists_iff_in_slab
#print axioms two_lifts_only_at_endpoint
#print axioms projected_edge_length

end NineSeparatedSubsetSums
