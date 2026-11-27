import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.EightPoint120_119Checked

namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem cachedEightPoint120_119_false : cachedFixedThirdShard 120 119 121795 = false := by decide +kernel

theorem eightPoint120_119_no_descending_tail : NoDescendingTailAfterThird 120 119 :=
  noDescendingThirdTail_of_cached 120 119 121795
    max148_second120_third119_eightPoint_moment_bound cachedEightPoint120_119_false

#print axioms cachedEightPoint120_119_false
#print axioms eightPoint120_119_no_descending_tail

end NineSeparatedSubsetSums
