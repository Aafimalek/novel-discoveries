import NineSeparatedSubsetSums.PairPackedShardsThrough103
import NineSeparatedSubsetSums.PairPackedShard104
import NineSeparatedSubsetSums.PairPackedShard105
import NineSeparatedSubsetSums.PairPackedShard106
import NineSeparatedSubsetSums.PairPackedShard107
import NineSeparatedSubsetSums.PairPackedShard108
import NineSeparatedSubsetSums.PairPackedShard109
import NineSeparatedSubsetSums.PairPackedShard110Split
import NineSeparatedSubsetSums.PairPackedShard111Split
import NineSeparatedSubsetSums.PairPackedShard112Split
import NineSeparatedSubsetSums.RealReduction
import Mathlib.Tactic.IntervalCases

open scoped BigOperators
namespace NineSeparatedSubsetSums

/-- Every fixed second-largest branch through 112 is kernel checked. -/
theorem pairPackedShardsThrough112Coverage (a : ℕ) (ha : a ≤ 112) :
    pair_packed_second_shard a = false := by
  by_cases small : a < 104
  · exact pairPackedShardsThrough103 ⟨a,small⟩
  · have hlow : 104 ≤ a := by omega
    interval_cases a
    · exact pairPackedShard104
    · exact pairPackedShard105
    · exact pairPackedShard106
    · exact pairPackedShard107
    · exact pairPackedShard108
    · exact pairPackedShard109
    · exact pairPackedShard110
    · exact pairPackedShard111
    · exact pairPackedShard112

/-- Precise remaining certificate obligation for the full real bound.
All preceding reductions and shards through 112 are checked. -/
theorem separated_nine_at_least_149_of_remaining_pair_packed_through112
    (checks : ∀ a : ℕ, 113 ≤ a → a ≤ 147 → pair_packed_second_shard a = false)
    (w : Fin 9 → ℝ) (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ i, 149 ≤ w i := by
  apply separated_nine_at_least_149_of_integer_exclusion _ w hpos sep
  intro a ha hmax hInj
  apply integer_max148_excluded_of_pair_packed_shards _ a
    (fun i => by have := (ha i).1; omega) (fun i => (ha i).2) hmax hInj
  intro a _ hhi
  by_cases hlow : a ≤ 112
  · exact pairPackedShardsThrough112Coverage a hlow
  · exact checks a (by omega) hhi

#print axioms pairPackedShardsThrough112Coverage
#print axioms separated_nine_at_least_149_of_remaining_pair_packed_through112

end NineSeparatedSubsetSums
