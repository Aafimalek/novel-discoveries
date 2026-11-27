import NineSeparatedSubsetSums.FourPoint133Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive133Third104
import NineSeparatedSubsetSums.Adaptive133Third105
import NineSeparatedSubsetSums.Adaptive133Third106
import NineSeparatedSubsetSums.Adaptive133Third107
import NineSeparatedSubsetSums.Adaptive133Third108
import NineSeparatedSubsetSums.Adaptive133Third109
import NineSeparatedSubsetSums.Adaptive133Third110
import NineSeparatedSubsetSums.Adaptive133Third111
import NineSeparatedSubsetSums.Adaptive133Third112
import NineSeparatedSubsetSums.Adaptive133Third113
import NineSeparatedSubsetSums.Adaptive133Third114
import NineSeparatedSubsetSums.Adaptive133Third115
import NineSeparatedSubsetSums.Adaptive133Third116
import NineSeparatedSubsetSums.Adaptive133Third117
import NineSeparatedSubsetSums.Adaptive133Third118
import NineSeparatedSubsetSums.Adaptive133Third119
import NineSeparatedSubsetSums.Adaptive133Third120
import NineSeparatedSubsetSums.Adaptive133Third121
import NineSeparatedSubsetSums.Adaptive133Third122
import NineSeparatedSubsetSums.Adaptive133Third123
import NineSeparatedSubsetSums.Adaptive133Third124
import NineSeparatedSubsetSums.Adaptive133Third125
import NineSeparatedSubsetSums.Adaptive133Third126
import NineSeparatedSubsetSums.Adaptive133Third127
import NineSeparatedSubsetSums.Adaptive133Third128
import NineSeparatedSubsetSums.Adaptive133Third129
import NineSeparatedSubsetSums.Adaptive133Third130
import NineSeparatedSubsetSums.Adaptive133Third131
import NineSeparatedSubsetSums.Adaptive133Third132

namespace NineSeparatedSubsetSums


theorem adaptiveShelf133_no_descending_tail : NoDescendingTail 133 := by
  apply noDescendingTail_of_third_tails 133 110552 max148_second133_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 133 110552 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive133Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive133Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive133Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive133Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive133Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive133Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive133Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive133Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive133Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive133Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive133Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive133Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive133Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive133Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive133Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive133Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive133Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive133Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive133Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive133Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive133Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive133Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive133Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive133Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive133Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive133Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive133Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive133Third131
  have hlast : b = 132 := by omega
  subst b
  exact adaptive133Third132

#print axioms adaptiveShelf133_no_descending_tail

end NineSeparatedSubsetSums
