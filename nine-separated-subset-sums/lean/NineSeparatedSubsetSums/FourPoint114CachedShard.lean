import NineSeparatedSubsetSums.FourPoint114Checked
import NineSeparatedSubsetSums.CachedFourPointShards

namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem cachedFourPoint114_false : cachedSecondShard 114 109216 = false := by decide +kernel

theorem fourPoint114_no_descending_tail : NoDescendingTail 114 :=
  noDescendingTail_of_cached 114 109216 max148_second114_fourPoint_moment_bound cachedFourPoint114_false

#print axioms cachedFourPoint114_false
#print axioms fourPoint114_no_descending_tail
end NineSeparatedSubsetSums
