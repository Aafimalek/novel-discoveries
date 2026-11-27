import NineSeparatedSubsetSums.CachedFourPointShards
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem cachedThird117Part3 : ∀ t : Fin 2, cachedThirdShard 117 109179 (t.val+6) = false := by decide +kernel
#print axioms cachedThird117Part3
