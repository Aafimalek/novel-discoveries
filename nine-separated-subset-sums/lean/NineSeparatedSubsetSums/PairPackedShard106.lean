import NineSeparatedSubsetSums.PairPackingWindowedCap
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem pairPackedShard106 : pair_packed_second_shard 106 = false := by decide +kernel
#print axioms pairPackedShard106
