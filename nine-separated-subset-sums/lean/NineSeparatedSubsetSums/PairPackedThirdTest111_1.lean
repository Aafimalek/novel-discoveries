import NineSeparatedSubsetSums.PairPackingThirdSplit
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem pairPackedThirdTest111_1 : pairPackedThirdShard 111 1 = false := by decide +kernel
#print axioms pairPackedThirdTest111_1
