import NineSeparatedSubsetSums.PairPackingWindowedCap
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem pairPackedShardsThrough103 : ∀ a : Fin 104, pair_packed_second_shard a.val = false := by decide +kernel
#print axioms pairPackedShardsThrough103
