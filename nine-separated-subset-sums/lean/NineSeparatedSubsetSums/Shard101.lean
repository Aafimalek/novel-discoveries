import NineSeparatedSubsetSums.IntegerShards
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 25000000 in
theorem shard_101_checked : integer_second_shard 101 = false := by decide
#print axioms shard_101_checked
