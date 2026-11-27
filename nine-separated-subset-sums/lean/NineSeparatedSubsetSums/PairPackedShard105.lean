import NineSeparatedSubsetSums.PairPackingWindowedCap
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem pairPackedShard105 : pair_packed_second_shard 105 = false := by decide +kernel
#print axioms pairPackedShard105
