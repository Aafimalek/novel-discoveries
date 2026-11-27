import NineSeparatedSubsetSums.CachedFourPointShards
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 100000000 in
theorem cachedFourPoint116_false : cachedSecondShard 116 109278 = false := by decide +kernel
#print axioms cachedFourPoint116_false
