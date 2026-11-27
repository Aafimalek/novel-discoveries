import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.EightPoint120_118Checked
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem cachedEightPoint120_118_false : cachedFixedThirdShard 120 118 121680 = false := by decide +kernel
theorem eightPoint120_118_no_descending_tail : NoDescendingTailAfterThird 120 118 :=
  noDescendingThirdTail_of_cached 120 118 121680
    max148_second120_third118_eightPoint_moment_bound cachedEightPoint120_118_false
#print axioms cachedEightPoint120_118_false
#print axioms eightPoint120_118_no_descending_tail
end NineSeparatedSubsetSums
