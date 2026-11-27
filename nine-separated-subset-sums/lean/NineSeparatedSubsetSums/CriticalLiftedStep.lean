import NineSeparatedSubsetSums.ProjectionLift
import NineSeparatedSubsetSums.RoundedInterval
import Mathlib.Tactic

namespace NineSeparatedSubsetSums

/-- Check rank orientation by the numeric scores within a consecutive score list. -/
private theorem le_index_of_le_score (v : ℕ → ℝ) (bound i j : ℕ)
    (hgap : ∀ k : ℕ, k + 1 < bound → 1 ≤ v (k + 1) - v k)
    (hi : i < bound) (hj : j < bound)
    (h : v i ≤ v j) : i ≤ j := by
  by_contra! hij
  have hsum := accumulate_gaps v bound hgap j (i - j) (by omega)
  have e : j + (i - j) = i := by omega
  rw [e] at hsum
  have hd : (0 : ℝ) < ((i - j : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < i - j by omega)
  linarith

def intLiftScore (s : ℤ) (b : Bool) : ℤ := s + if b then 148 else 0

/-- A single projected add-coordinate edge preserves the offset, in any
choice of the two lifts in the critical interval. -/
theorem lifted_insert_preserves_offset
    (v : ℕ → ℝ) (bound L R i j : ℕ) (s x M δ : ℝ) (a : ℤ) (b c : Bool)
    (hgap : ∀ k : ℕ, k + 1 < bound → 1 ≤ v (k + 1) - v k)
    (hLi : L ≤ i) (hiR : i ≤ R) (hLj : L ≤ j) (hjR : j ≤ R) (hRb : R < bound)
    (hexcess : v R - v L - ((R - L : ℕ) : ℝ) < 1)
    (hwidth : v R - v L = M) (hδ : 0 ≤ δ ∧ δ < 1) (hM : M = 148 + δ)
    (hx : 0 < x) (hxM : x ≤ M) (hfrac : Int.fract x ≤ δ)
    (hi : v i = liftScore M s b) (hj : v j = liftScore M (s + x) c) :
    (i : ℤ) - intLiftScore a b = (j : ℤ) - intLiftScore (a + ⌊x⌋) c := by
  have hi' : i < bound := by omega
  have hj' : j < bound := by omega
  have dlo (k : ℕ) (hk : L ≤ k) (hk' : k ≤ R) : v L ≤ v k := by
    have ha := accumulate_gaps v bound hgap L (k - L) (by omega)
    have he : L + (k - L) = k := by omega
    rw [he] at ha
    linarith [Nat.cast_nonneg (α := ℝ) (k - L)]
  have dhi (k : ℕ) (hk : L ≤ k) (hk' : k ≤ R) : v k ≤ v R := by
    have ha := accumulate_gaps v bound hgap k (R - k) (by omega)
    have he : k + (R - k) = R := by omega
    rw [he] at ha
    linarith [Nat.cast_nonneg (α := ℝ) (R - k)]
  cases b <;> cases c
  · have he : v j - v i = x := by simp [hi, hj, liftScore] <;> ring
    have hle := le_index_of_le_score v bound i j hgap hi' hj' (by linarith)
    have hs := rank_difference_is_floor v bound L R i j hgap hLi hle hjR hRb hexcess
    rw [he] at hs
    simp only [intLiftScore, Bool.false_eq_true, ite_false, add_zero]
    omega
  · exfalso
    have he : v j - v i = x + M := by simp [hi, hj, liftScore] <;> ring
    linarith [dlo i hLi hiR, dhi j hLj hjR]
  · have he : v i - v j = M - x := by simp [hi, hj, liftScore] <;> ring
    have hle := le_index_of_le_score v bound j i hgap hj' hi' (by linarith)
    have hs : ⌊v i - v j⌋ = 148 - ⌊x⌋ := by
      rw [he, floorCriticalCompl M x δ hM hδ hfrac]
    rw [rank_difference_is_floor v bound L R j i hgap hLj hle hiR hRb hexcess] at hs
    simp only [intLiftScore, ite_true, Bool.false_eq_true, ite_false, add_zero]
    omega
  · have he : v j - v i = x := by simp [hi, hj, liftScore] <;> ring
    have hle := le_index_of_le_score v bound i j hgap hi' hj' (by linarith)
    have hs := rank_difference_is_floor v bound L R i j hgap hLi hle hjR hRb hexcess
    rw [he] at hs
    simp only [intLiftScore, ite_true]
    omega

#print axioms lifted_insert_preserves_offset

end NineSeparatedSubsetSums
