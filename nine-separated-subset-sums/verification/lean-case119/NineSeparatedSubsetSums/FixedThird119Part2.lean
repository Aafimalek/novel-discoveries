import NineSeparatedSubsetSums.CachedFixedThird
open NineSeparatedSubsetSums
set_option maxRecDepth 47000 in
set_option maxHeartbeats 300000000 in
theorem fixedThird119Part2 : ∀ t : Fin 1,
    cachedFixedThirdShard 119 (114+t.val) 108780 = false := by decide +kernel
#print axioms fixedThird119Part2
