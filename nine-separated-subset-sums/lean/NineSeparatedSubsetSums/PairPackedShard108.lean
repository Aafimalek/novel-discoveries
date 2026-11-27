import NineSeparatedSubsetSums.PairPackingWindowedCap
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem pairPackedShard108 : pair_packed_second_shard 108 = false := by decide +kernel
#print axioms pairPackedShard108
