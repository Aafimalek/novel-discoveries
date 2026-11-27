import NineSeparatedSubsetSums.CachedFixedThird
open NineSeparatedSubsetSums
set_option maxRecDepth 47000 in
set_option maxHeartbeats 300000000 in
theorem fixedThird119Part1 : ∀ t : Fin 2,
    cachedFixedThirdShard 119 (112+t.val) 108780 = false := by decide +kernel
#print axioms fixedThird119Part1
