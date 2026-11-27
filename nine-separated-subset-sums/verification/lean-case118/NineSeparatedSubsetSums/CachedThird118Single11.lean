import NineSeparatedSubsetSums.CachedFourPointShards
open NineSeparatedSubsetSums
set_option maxRecDepth 40000 in
set_option maxHeartbeats 240000000 in
theorem cachedThird118Single11 : cachedThirdShard 118 109014 11 = false := by decide +kernel
#print axioms cachedThird118Single11
