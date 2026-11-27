import NineSeparatedSubsetSums.CachedFourPointShards
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem cachedThird118Part1 : ∀ t : Fin 2, cachedThirdShard 118 109014 (t.val+2) = false := by decide +kernel
#print axioms cachedThird118Part1
