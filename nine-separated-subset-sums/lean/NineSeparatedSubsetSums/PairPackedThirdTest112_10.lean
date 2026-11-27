import NineSeparatedSubsetSums.PairPackingThirdSplit
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem pairPackedThirdTest112_10 : pairPackedThirdShard 112 10 = false := by decide +kernel
#print axioms pairPackedThirdTest112_10
