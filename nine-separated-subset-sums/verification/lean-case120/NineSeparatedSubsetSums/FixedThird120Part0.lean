import NineSeparatedSubsetSums.CachedFixedThird
open NineSeparatedSubsetSums
set_option maxRecDepth 47000 in
set_option maxHeartbeats 300000000 in
theorem fixedThird120Part0 : ∀ t : Fin 7,
    cachedFixedThirdShard 120 (105+t.val) 108497 = false := by decide +kernel
#print axioms fixedThird120Part0
