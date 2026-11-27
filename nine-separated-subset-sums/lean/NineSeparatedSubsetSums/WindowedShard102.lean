import NineSeparatedSubsetSums.IntegerSearchWindowed
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 30000000 in
theorem windowedShard_102_checked : windowed_second_shard 102 = false := by decide +kernel
#print axioms windowedShard_102_checked
