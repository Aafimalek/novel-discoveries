import NineSeparatedSubsetSums.FourPoint134Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive134Third104
import NineSeparatedSubsetSums.Adaptive134Third105
import NineSeparatedSubsetSums.Adaptive134Third106
import NineSeparatedSubsetSums.Adaptive134Third107
import NineSeparatedSubsetSums.Adaptive134Third108
import NineSeparatedSubsetSums.Adaptive134Third109
import NineSeparatedSubsetSums.Adaptive134Third110
import NineSeparatedSubsetSums.Adaptive134Third111
import NineSeparatedSubsetSums.Adaptive134Third112
import NineSeparatedSubsetSums.Adaptive134Third113
import NineSeparatedSubsetSums.Adaptive134Third114
import NineSeparatedSubsetSums.Adaptive134Third115
import NineSeparatedSubsetSums.Adaptive134Third116
import NineSeparatedSubsetSums.Adaptive134Third117
import NineSeparatedSubsetSums.Adaptive134Third118
import NineSeparatedSubsetSums.Adaptive134Third119
import NineSeparatedSubsetSums.Adaptive134Third120
import NineSeparatedSubsetSums.Adaptive134Third121
import NineSeparatedSubsetSums.Adaptive134Third122
import NineSeparatedSubsetSums.Adaptive134Third123
import NineSeparatedSubsetSums.Adaptive134Third124
import NineSeparatedSubsetSums.Adaptive134Third125
import NineSeparatedSubsetSums.Adaptive134Third126
import NineSeparatedSubsetSums.Adaptive134Third127
import NineSeparatedSubsetSums.Adaptive134Third128
import NineSeparatedSubsetSums.Adaptive134Third129
import NineSeparatedSubsetSums.Adaptive134Third130
import NineSeparatedSubsetSums.Adaptive134Third131
import NineSeparatedSubsetSums.Adaptive134Third132
import NineSeparatedSubsetSums.Adaptive134Third133

namespace NineSeparatedSubsetSums


theorem adaptiveShelf134_no_descending_tail : NoDescendingTail 134 := by
  apply noDescendingTail_of_third_tails 134 110531 max148_second134_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 134 110531 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive134Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive134Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive134Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive134Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive134Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive134Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive134Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive134Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive134Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive134Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive134Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive134Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive134Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive134Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive134Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive134Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive134Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive134Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive134Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive134Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive134Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive134Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive134Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive134Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive134Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive134Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive134Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive134Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive134Third132
  have hlast : b = 133 := by omega
  subst b
  exact adaptive134Third133

#print axioms adaptiveShelf134_no_descending_tail

end NineSeparatedSubsetSums
