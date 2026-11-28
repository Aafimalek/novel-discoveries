import NineSeparatedSubsetSums.GenericAssembly147
import NineSeparatedSubsetSums.ClosedTailRange122
import NineSeparatedSubsetSums.AdaptiveShelf123
import NineSeparatedSubsetSums.AdaptiveShelf124
import NineSeparatedSubsetSums.AdaptiveShelf125
import NineSeparatedSubsetSums.AdaptiveShelf126
import NineSeparatedSubsetSums.AdaptiveShelf127
import NineSeparatedSubsetSums.AdaptiveShelf128
import NineSeparatedSubsetSums.AdaptiveShelf129
import NineSeparatedSubsetSums.AdaptiveShelf130
import NineSeparatedSubsetSums.AdaptiveShelf131
import NineSeparatedSubsetSums.AdaptiveShelf132
import NineSeparatedSubsetSums.AdaptiveShelf133
import NineSeparatedSubsetSums.AdaptiveShelf134
import NineSeparatedSubsetSums.AdaptiveShelf135
import NineSeparatedSubsetSums.AdaptiveShelf136
import NineSeparatedSubsetSums.AdaptiveShelf137
import NineSeparatedSubsetSums.AdaptiveShelf138
import NineSeparatedSubsetSums.AdaptiveShelf139
import NineSeparatedSubsetSums.AdaptiveShelf140
import NineSeparatedSubsetSums.AdaptiveShelf141
import NineSeparatedSubsetSums.AdaptiveShelf142
import NineSeparatedSubsetSums.AdaptiveShelf143
import NineSeparatedSubsetSums.AdaptiveShelf144
import NineSeparatedSubsetSums.AdaptiveShelf145
import NineSeparatedSubsetSums.AdaptiveShelf146
import NineSeparatedSubsetSums.AdaptiveShelf147

open scoped BigOperators
namespace NineSeparatedSubsetSums

/-- Certificate application only: no arithmetic tactic runs in this module. -/
theorem separated_nine_at_least_149
    (w : Fin 9 → ℝ) (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ i, 149 ≤ w i :=
  genericAssembly147
    noDescendingTailsThrough122
    adaptiveShelf123_no_descending_tail
    adaptiveShelf124_no_descending_tail
    adaptiveShelf125_no_descending_tail
    adaptiveShelf126_no_descending_tail
    adaptiveShelf127_no_descending_tail
    adaptiveShelf128_no_descending_tail
    adaptiveShelf129_no_descending_tail
    adaptiveShelf130_no_descending_tail
    adaptiveShelf131_no_descending_tail
    adaptiveShelf132_no_descending_tail
    adaptiveShelf133_no_descending_tail
    adaptiveShelf134_no_descending_tail
    adaptiveShelf135_no_descending_tail
    adaptiveShelf136_no_descending_tail
    adaptiveShelf137_no_descending_tail
    adaptiveShelf138_no_descending_tail
    adaptiveShelf139_no_descending_tail
    adaptiveShelf140_no_descending_tail
    adaptiveShelf141_no_descending_tail
    adaptiveShelf142_no_descending_tail
    adaptiveShelf143_no_descending_tail
    adaptiveShelf144_no_descending_tail
    adaptiveShelf145_no_descending_tail
    adaptiveShelf146_no_descending_tail
    adaptiveShelf147_no_descending_tail
    w hpos sep

end NineSeparatedSubsetSums
