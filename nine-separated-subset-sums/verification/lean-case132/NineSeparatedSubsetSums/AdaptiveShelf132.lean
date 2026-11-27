import NineSeparatedSubsetSums.FourPoint132Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive132Third104
import NineSeparatedSubsetSums.Adaptive132Third105
import NineSeparatedSubsetSums.Adaptive132Third106
import NineSeparatedSubsetSums.Adaptive132Third107
import NineSeparatedSubsetSums.Adaptive132Third108
import NineSeparatedSubsetSums.Adaptive132Third109
import NineSeparatedSubsetSums.Adaptive132Third110
import NineSeparatedSubsetSums.Adaptive132Third111
import NineSeparatedSubsetSums.Adaptive132Third112
import NineSeparatedSubsetSums.Adaptive132Third113
import NineSeparatedSubsetSums.Adaptive132Third114
import NineSeparatedSubsetSums.Adaptive132Third115
import NineSeparatedSubsetSums.Adaptive132Third116
import NineSeparatedSubsetSums.Adaptive132Third117
import NineSeparatedSubsetSums.Adaptive132Third118
import NineSeparatedSubsetSums.Adaptive132Third119
import NineSeparatedSubsetSums.Adaptive132Third120
import NineSeparatedSubsetSums.Adaptive132Third121
import NineSeparatedSubsetSums.Adaptive132Third122
import NineSeparatedSubsetSums.Adaptive132Third123
import NineSeparatedSubsetSums.Adaptive132Third124
import NineSeparatedSubsetSums.Adaptive132Third125
import NineSeparatedSubsetSums.Adaptive132Third126
import NineSeparatedSubsetSums.Adaptive132Third127
import NineSeparatedSubsetSums.Adaptive132Third128
import NineSeparatedSubsetSums.Adaptive132Third129
import NineSeparatedSubsetSums.Adaptive132Third130
import NineSeparatedSubsetSums.Adaptive132Third131

namespace NineSeparatedSubsetSums


theorem adaptiveShelf132_no_descending_tail : NoDescendingTail 132 := by
  apply noDescendingTail_of_third_tails 132 110282 max148_second132_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 132 110282 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive132Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive132Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive132Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive132Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive132Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive132Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive132Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive132Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive132Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive132Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive132Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive132Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive132Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive132Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive132Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive132Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive132Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive132Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive132Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive132Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive132Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive132Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive132Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive132Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive132Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive132Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive132Third130
  have hlast : b = 131 := by omega
  subst b
  exact adaptive132Third131

#print axioms adaptiveShelf132_no_descending_tail

end NineSeparatedSubsetSums
