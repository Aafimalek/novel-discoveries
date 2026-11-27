import NineSeparatedSubsetSums.PairPackedThirdTest111_0
import NineSeparatedSubsetSums.PairPackedThirdTest111_1
import NineSeparatedSubsetSums.PairPackedThirdTest111_2
import NineSeparatedSubsetSums.PairPackedThirdTest111_3
import NineSeparatedSubsetSums.PairPackedThirdTest111_4
import NineSeparatedSubsetSums.PairPackedThirdTest111_5
import NineSeparatedSubsetSums.PairPackedThirdTest111_6
import NineSeparatedSubsetSums.PairPackedThirdTest111_7
import NineSeparatedSubsetSums.PairPackedThirdTest111_8
import Mathlib.Tactic.IntervalCases

open NineSeparatedSubsetSums

theorem pairPackedShard111 : pair_packed_second_shard 111 = false := by
  apply pairPackedSecondFalse_of_third 111
  intro t ht
  have hcount : pairPackedThirdCount 111 = 9 := by decide +kernel
  rw [hcount] at ht
  interval_cases t
  · exact pairPackedThirdTest111_0
  · exact pairPackedThirdTest111_1
  · exact pairPackedThirdTest111_2
  · exact pairPackedThirdTest111_3
  · exact pairPackedThirdTest111_4
  · exact pairPackedThirdTest111_5
  · exact pairPackedThirdTest111_6
  · exact pairPackedThirdTest111_7
  · exact pairPackedThirdTest111_8

#print axioms pairPackedShard111
