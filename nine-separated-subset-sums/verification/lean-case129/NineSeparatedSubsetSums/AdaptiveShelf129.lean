import NineSeparatedSubsetSums.FourPoint129Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive129Third104
import NineSeparatedSubsetSums.Adaptive129Third105
import NineSeparatedSubsetSums.Adaptive129Third106
import NineSeparatedSubsetSums.Adaptive129Third107
import NineSeparatedSubsetSums.Adaptive129Third108
import NineSeparatedSubsetSums.Adaptive129Third109
import NineSeparatedSubsetSums.Adaptive129Third110
import NineSeparatedSubsetSums.Adaptive129Third111
import NineSeparatedSubsetSums.Adaptive129Third112
import NineSeparatedSubsetSums.Adaptive129Third113
import NineSeparatedSubsetSums.Adaptive129Third114
import NineSeparatedSubsetSums.Adaptive129Third115
import NineSeparatedSubsetSums.Adaptive129Third116
import NineSeparatedSubsetSums.Adaptive129Third117
import NineSeparatedSubsetSums.Adaptive129Third118
import NineSeparatedSubsetSums.Adaptive129Third119
import NineSeparatedSubsetSums.Adaptive129Third120
import NineSeparatedSubsetSums.Adaptive129Third121
import NineSeparatedSubsetSums.Adaptive129Third122
import NineSeparatedSubsetSums.Adaptive129Third123
import NineSeparatedSubsetSums.Adaptive129Third124
import NineSeparatedSubsetSums.Adaptive129Third125
import NineSeparatedSubsetSums.Adaptive129Third126
import NineSeparatedSubsetSums.Adaptive129Third127
import NineSeparatedSubsetSums.Adaptive129Third128

namespace NineSeparatedSubsetSums


theorem adaptiveShelf129_no_descending_tail : NoDescendingTail 129 := by
  apply noDescendingTail_of_third_tails 129 109587 max148_second129_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 129 109587 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive129Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive129Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive129Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive129Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive129Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive129Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive129Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive129Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive129Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive129Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive129Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive129Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive129Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive129Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive129Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive129Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive129Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive129Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive129Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive129Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive129Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive129Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive129Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive129Third127
  have hlast : b = 128 := by omega
  subst b
  exact adaptive129Third128

#print axioms adaptiveShelf129_no_descending_tail

end NineSeparatedSubsetSums
