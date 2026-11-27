import NineSeparatedSubsetSums.CachedFourPointShards
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 100000000 in
theorem cachedFourPoint115_false : cachedSecondShard 115 109254 = false := by decide +kernel
#print axioms cachedFourPoint115_false
