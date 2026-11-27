import NineSeparatedSubsetSums.PairPackingThirdSplit
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem pairPackedThirdTest111_8 : pairPackedThirdShard 111 8 = false := by decide +kernel
#print axioms pairPackedThirdTest111_8
