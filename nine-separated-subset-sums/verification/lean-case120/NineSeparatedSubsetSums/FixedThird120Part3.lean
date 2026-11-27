import NineSeparatedSubsetSums.CachedFixedThird
open NineSeparatedSubsetSums
set_option maxRecDepth 47000 in
set_option maxHeartbeats 300000000 in
theorem fixedThird120Part3 : ∀ t : Fin 1,
    cachedFixedThirdShard 120 (115+t.val) 108497 = false := by decide +kernel
#print axioms fixedThird120Part3
