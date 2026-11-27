import NineSeparatedSubsetSums.IntegerSearchWindowedCap
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem capShard_104_checked : windowed_cap_second_shard 104 = false := by decide +kernel
#print axioms capShard_104_checked
