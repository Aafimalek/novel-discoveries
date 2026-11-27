import NineSeparatedSubsetSums.PairPackedThirdTest112_0
import NineSeparatedSubsetSums.PairPackedThirdTest112_1
import NineSeparatedSubsetSums.PairPackedThirdTest112_2
import NineSeparatedSubsetSums.PairPackedThirdTest112_3
import NineSeparatedSubsetSums.PairPackedThirdTest112_4
import NineSeparatedSubsetSums.PairPackedThirdTest112_5
import NineSeparatedSubsetSums.PairPackedThirdTest112_6
import NineSeparatedSubsetSums.PairPackedThirdTest112_7
import NineSeparatedSubsetSums.PairPackedThirdTest112_8
import NineSeparatedSubsetSums.PairPackedThirdTest112_9
import NineSeparatedSubsetSums.PairPackedThirdTest112_10
import Mathlib.Tactic.IntervalCases

open NineSeparatedSubsetSums

theorem pairPackedShard112 : pair_packed_second_shard 112 = false := by
  apply pairPackedSecondFalse_of_third 112
  intro t ht
  have hcount : pairPackedThirdCount 112 = 11 := by decide +kernel
  rw [hcount] at ht
  interval_cases t
  · exact pairPackedThirdTest112_0
  · exact pairPackedThirdTest112_1
  · exact pairPackedThirdTest112_2
  · exact pairPackedThirdTest112_3
  · exact pairPackedThirdTest112_4
  · exact pairPackedThirdTest112_5
  · exact pairPackedThirdTest112_6
  · exact pairPackedThirdTest112_7
  · exact pairPackedThirdTest112_8
  · exact pairPackedThirdTest112_9
  · exact pairPackedThirdTest112_10

#print axioms pairPackedShard112
