import NineSeparatedSubsetSums.CachedFourPointShards
open NineSeparatedSubsetSums
set_option maxRecDepth 40000 in
set_option maxHeartbeats 240000000 in
theorem cachedThird118Single10 : cachedThirdShard 118 109014 10 = false := by decide +kernel
#print axioms cachedThird118Single10
