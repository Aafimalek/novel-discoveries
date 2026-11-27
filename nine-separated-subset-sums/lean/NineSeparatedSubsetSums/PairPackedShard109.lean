import NineSeparatedSubsetSums.PairPackingWindowedCap
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem pairPackedShard109 : pair_packed_second_shard 109 = false := by decide +kernel
#print axioms pairPackedShard109
