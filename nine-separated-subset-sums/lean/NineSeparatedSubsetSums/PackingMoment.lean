import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace NineSeparatedSubsetSums

theorem oddSquares (n : ℕ) :
    3 * (∑ i ∈ Finset.range n, (2 * (i : ℤ) + 1)^2) = (n : ℤ) * (4 * (n : ℤ)^2 - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ, mul_add, ih]
    ring

/-- Least second moment of 512 real-centered signed sums in a parity class.
Here `f` enumerates the signed sums in increasing order. -/
theorem momentOfRankedSignedScores (f : ℕ → ℤ)
    (gap : ∀ i j : ℕ, i ≤ j → j < 512 → 2 * ((j : ℤ) - (i : ℤ)) ≤ f j - f i) :
    44739072 ≤ ∑ i ∈ Finset.range 512, (f i)^2 := by
  have odd : (∑ i ∈ Finset.range 256, (2 * (i : ℤ) + 1)^2) = 22369536 := by
    have h := oddSquares 256
    norm_num at h
    omega
  have pa : ∀ i ∈ Finset.range 256,
      2 * (2 * (i : ℤ) + 1)^2 ≤ (f (255 - i))^2 + (f (256 + i))^2 := by
    intro i hi
    have hι := Finset.mem_range.mp hi
    have hj : 255 - i ≤ 256 + i := by omega
    have hjo : 256 + i < 512 := by omega
    have hx := gap (255 - i) (256 + i) hj hjo
    have hr : ((256 + i : ℕ) : ℤ) - ((255 - i : ℕ) : ℤ) = 2 * (i : ℤ) + 1 := by
      omega
    rw [hr] at hx
    have hpos : 0 ≤ f (256+i) - f (255-i) - 2*(2*(i : ℤ)+1) := by omega
    have hpos' : 0 ≤ f (256+i) - f (255-i) + 2*(2*(i : ℤ)+1) := by omega
    nlinarith only [mul_nonneg hpos hpos', sq_nonneg (f (256+i)+f (255-i))]
  have lhs : (∑ i ∈ Finset.range 256, 2 * (2 * (i : ℤ) + 1)^2) = 44739072 := by
    rw [← Finset.mul_sum, odd]
    norm_num
  have rhs : (∑ i ∈ Finset.range 256, ((f (255-i))^2 + (f (256+i))^2)) =
      (∑ i ∈ Finset.range 512, (f i)^2) := by
    rw [Finset.sum_add_distrib]
    have h1 := Finset.sum_range_reflect (fun i => (f i)^2) 256
    rw [show 256 - 1 = 255 by decide] at h1
    rw [h1]
    rw [show 512 = 256 + 256 by decide, Finset.sum_range_add]
  have hy := Finset.sum_le_sum pa
  rw [lhs, rhs] at hy
  exact hy

#print axioms oddSquares
#print axioms momentOfRankedSignedScores

end NineSeparatedSubsetSums
