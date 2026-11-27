import NineSeparatedSubsetSums.FourPointSymmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

open scoped BigOperators

namespace NineSeparatedSubsetSums

private theorem listNatLookup_sum (l : List ℕ) :
    (∑ i ∈ Finset.range l.length, ((l[i]?.getD 0 : ℕ) : ℤ)) = (l.sum : ℤ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, ih, List.sum_cons, Nat.cast_add, add_comm]

/-- The full symmetric penalty budget can be replayed by one linear
array sum; no repeated index lookup across the box is necessary. -/
theorem fourPointLookupBudget_eq (T : Array ℕ) :
    (∑ z ∈ fourPointLookupBox T, fourPointLookupPenalty T z) =
      2*(T.toList.sum : ℤ) - fourPointLookupPenalty T 0 := by
  rw [fourPointLookupBox, Finset.sum_Icc_of_even_eq_range
    (fourPointLookupPenalty_neg T) T.size, Finset.sum_range_succ]
  have tail : fourPointLookupPenalty T (T.size : ℤ) = 0 := by
    simp [fourPointLookupPenalty, Array.getElem?_eq_none (Nat.le_refl T.size)]
  rw [tail, add_zero]
  have mid : (∑ z ∈ Finset.range T.size, fourPointLookupPenalty T (z : ℤ)) =
      (T.toList.sum : ℤ) := by
    simpa only [fourPointLookupPenalty, Int.natAbs_natCast, Array.getElem?_toList,
      Array.length_toList] using listNatLookup_sum T.toList
  rw [mid, nsmul_eq_mul]
  rfl

#print axioms fourPointLookupBudget_eq

end NineSeparatedSubsetSums
