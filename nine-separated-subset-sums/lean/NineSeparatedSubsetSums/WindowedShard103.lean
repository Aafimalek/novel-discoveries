import NineSeparatedSubsetSums.IntegerSearchWindowed
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 30000000 in
theorem windowedShard_103_checked : windowed_second_shard 103 = false := by decide +kernel
#print axioms windowedShard_103_checked
