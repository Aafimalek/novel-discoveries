import NineSeparatedSubsetSums.PairPackedShardsThrough103
import NineSeparatedSubsetSums.PairPackedShard104
import NineSeparatedSubsetSums.PairPackedShard105
import NineSeparatedSubsetSums.PairPackedShard106
import NineSeparatedSubsetSums.PairPackedShard107
import NineSeparatedSubsetSums.PairPackedShard108
import NineSeparatedSubsetSums.PairPackedShard109
import NineSeparatedSubsetSums.RealReduction
import Mathlib.Tactic.IntervalCases

open scoped BigOperators
namespace NineSeparatedSubsetSums

/-- Every fixed second-largest branch through 109 is kernel checked. -/
theorem pairPackedShardsThrough109Coverage (a : ℕ) (ha : a ≤ 109) :
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

/-- Precise remaining certificate obligation for the full real bound.
All preceding reductions and shards through 109 are checked. -/
theorem separated_nine_at_least_149_of_remaining_pair_packed_through109
    (checks : ∀ a : ℕ, 110 ≤ a → a ≤ 147 → pair_packed_second_shard a = false)
    (w : Fin 9 → ℝ) (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ i, 149 ≤ w i := by
  apply separated_nine_at_least_149_of_integer_exclusion _ w hpos sep
  intro a ha hmax hInj
  apply integer_max148_excluded_of_pair_packed_shards _ a
    (fun i => by have := (ha i).1; omega) (fun i => (ha i).2) hmax hInj
  intro a _ hhi
  by_cases hlow : a ≤ 109
  · exact pairPackedShardsThrough109Coverage a hlow
  · exact checks a (by omega) hhi

#print axioms pairPackedShardsThrough109Coverage
#print axioms separated_nine_at_least_149_of_remaining_pair_packed_through109

end NineSeparatedSubsetSums
