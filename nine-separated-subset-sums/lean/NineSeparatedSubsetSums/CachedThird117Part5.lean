import NineSeparatedSubsetSums.CachedFourPointShards
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem cachedThird117Part5 : ∀ t : Fin 1, cachedThirdShard 117 109179 (t.val+10) = false := by decide +kernel
#print axioms cachedThird117Part5
