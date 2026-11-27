import NineSeparatedSubsetSums.IntegerShards
open NineSeparatedSubsetSums

set_option maxRecDepth 16384 in
set_option maxHeartbeats 30000000 in
theorem shard_100_checked : integer_second_shard 100 = false := by decide

#print axioms shard_100_checked
