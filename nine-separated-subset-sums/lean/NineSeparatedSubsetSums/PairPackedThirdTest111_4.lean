import NineSeparatedSubsetSums.PairPackingThirdSplit
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem pairPackedThirdTest111_4 : pairPackedThirdShard 111 4 = false := by decide +kernel
#print axioms pairPackedThirdTest111_4
