import NineSeparatedSubsetSums.PairPackedThirdTest110_0
import NineSeparatedSubsetSums.PairPackedThirdTest110_1
import NineSeparatedSubsetSums.PairPackedThirdTest110_2
import NineSeparatedSubsetSums.PairPackedThirdTest110_3
import NineSeparatedSubsetSums.PairPackedThirdTest110_4
import NineSeparatedSubsetSums.PairPackedThirdTest110_5
import NineSeparatedSubsetSums.PairPackedThirdTest110_6
import NineSeparatedSubsetSums.PairPackedThirdTest110_7
import Mathlib.Tactic.IntervalCases

open NineSeparatedSubsetSums

theorem pairPackedShard110 : pair_packed_second_shard 110 = false := by
  apply pairPackedSecondFalse_of_third 110
  intro t ht
  have hcount : pairPackedThirdCount 110 = 8 := by decide +kernel
  rw [hcount] at ht
  interval_cases t
  · exact pairPackedThirdTest110_0
  · exact pairPackedThirdTest110_1
  · exact pairPackedThirdTest110_2
  · exact pairPackedThirdTest110_3
  · exact pairPackedThirdTest110_4
  · exact pairPackedThirdTest110_5
  · exact pairPackedThirdTest110_6
  · exact pairPackedThirdTest110_7

#print axioms pairPackedShard110
