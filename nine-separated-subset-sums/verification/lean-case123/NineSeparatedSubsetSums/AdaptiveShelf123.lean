import NineSeparatedSubsetSums.FourPoint123Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive123Third105
import NineSeparatedSubsetSums.Adaptive123Third106
import NineSeparatedSubsetSums.Adaptive123Third107
import NineSeparatedSubsetSums.Adaptive123Third108
import NineSeparatedSubsetSums.Adaptive123Third109
import NineSeparatedSubsetSums.Adaptive123Third110
import NineSeparatedSubsetSums.Adaptive123Third111
import NineSeparatedSubsetSums.Adaptive123Third112
import NineSeparatedSubsetSums.Adaptive123Third113
import NineSeparatedSubsetSums.Adaptive123Third114
import NineSeparatedSubsetSums.Adaptive123Third115
import NineSeparatedSubsetSums.Adaptive123Third116
import NineSeparatedSubsetSums.Adaptive123Third117
import NineSeparatedSubsetSums.Adaptive123Third118
import NineSeparatedSubsetSums.Adaptive123Third119
import NineSeparatedSubsetSums.Adaptive123Third120
import NineSeparatedSubsetSums.Adaptive123Third121
import NineSeparatedSubsetSums.Adaptive123Third122

namespace NineSeparatedSubsetSums


theorem adaptiveShelf123_no_descending_tail : NoDescendingTail 123 := by
  apply noDescendingTail_of_third_tails 123 109206 max148_second123_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 123 109206 = 105 := by decide +kernel
  rw [cut] at hlo
  by_cases h105 : b = 105
  · subst b; exact adaptive123Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive123Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive123Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive123Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive123Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive123Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive123Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive123Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive123Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive123Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive123Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive123Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive123Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive123Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive123Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive123Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive123Third121
  have hlast : b = 122 := by omega
  subst b
  exact adaptive123Third122

#print axioms adaptiveShelf123_no_descending_tail

end NineSeparatedSubsetSums
