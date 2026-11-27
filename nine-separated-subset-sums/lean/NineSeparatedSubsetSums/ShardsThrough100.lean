import NineSeparatedSubsetSums.IntegerShards
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in
theorem all_shards_through_100 : ∀ a : Fin 101, integer_second_shard a.val = false := by decide
#print axioms all_shards_through_100
