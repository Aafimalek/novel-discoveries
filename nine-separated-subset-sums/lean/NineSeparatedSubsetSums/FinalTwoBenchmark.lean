import NineSeparatedSubsetSums.FinalTwoSearch

namespace NineSeparatedSubsetSums

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- A single concrete prefix from the nine-weight max-148 search size. -/
def finalTwoBenchPrefix : List ℕ := [148,110,106,96,94,85,82]

set_option profiler true in
/-- Fixed representative tiny shard only, not the full exclusion. -/
theorem finalTwoBenchFalse :
    finalTwoSearch finalTwoBenchPrefix 511 87381 72 81 = false := by decide +kernel

theorem finalTwoBenchPrefixValid : (computeSubsetMask finalTwoBenchPrefix).2 = true := by
  decide

/-- The false benchmark Boolean and the checked helper exclude exactly the
tail pairs selected by this prefix, closed a interval, and the two bounds. -/
theorem finalTwoBenchShardExcluded (a b : ℕ) (ha₁ : 72 ≤ a) (ha₂ : a ≤ 81)
    (hb₁ : 0 < b) (hb₂ : b < a)
    (hs : 511 ≤ 721+a+b) (hq : 87381 ≤ 77241+a^2+b^2) :
    ¬ (natSubsetSums (finalTwoBenchPrefix ++ [a,b])).Nodup :=
  no_finalTwo_of_false finalTwoBenchPrefix
    ((computeSubsetMask_correct finalTwoBenchPrefix).2.mp finalTwoBenchPrefixValid)
    511 87381 72 81 (by decide) finalTwoBenchFalse a b ha₁ ha₂ hb₁ hb₂ hs hq

/-- Positive control: 8,4 can extend to the distinct-sums powers 8,4,2,1. -/
theorem finalTwoBenchPositive :
    finalTwoSearch [8,4] 15 85 2 2 = true := by decide

theorem finalTwoBenchEmpty :
    finalTwoSearch [8,4] 15 85 3 1 = false := by decide

#print axioms finalTwoBenchFalse
#print axioms finalTwoBenchShardExcluded
#print axioms finalTwoBenchPositive

end NineSeparatedSubsetSums
