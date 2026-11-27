import NineSeparatedSubsetSums.PairPackingThirdSplit
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem pairPackedThirdTest110_0 : pairPackedThirdShard 110 0 = false := by decide +kernel
#print axioms pairPackedThirdTest110_0
