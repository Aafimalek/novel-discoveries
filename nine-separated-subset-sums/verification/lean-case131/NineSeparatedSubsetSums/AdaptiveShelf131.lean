import NineSeparatedSubsetSums.FourPoint131Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive131Third104
import NineSeparatedSubsetSums.Adaptive131Third105
import NineSeparatedSubsetSums.Adaptive131Third106
import NineSeparatedSubsetSums.Adaptive131Third107
import NineSeparatedSubsetSums.Adaptive131Third108
import NineSeparatedSubsetSums.Adaptive131Third109
import NineSeparatedSubsetSums.Adaptive131Third110
import NineSeparatedSubsetSums.Adaptive131Third111
import NineSeparatedSubsetSums.Adaptive131Third112
import NineSeparatedSubsetSums.Adaptive131Third113
import NineSeparatedSubsetSums.Adaptive131Third114
import NineSeparatedSubsetSums.Adaptive131Third115
import NineSeparatedSubsetSums.Adaptive131Third116
import NineSeparatedSubsetSums.Adaptive131Third117
import NineSeparatedSubsetSums.Adaptive131Third118
import NineSeparatedSubsetSums.Adaptive131Third119
import NineSeparatedSubsetSums.Adaptive131Third120
import NineSeparatedSubsetSums.Adaptive131Third121
import NineSeparatedSubsetSums.Adaptive131Third122
import NineSeparatedSubsetSums.Adaptive131Third123
import NineSeparatedSubsetSums.Adaptive131Third124
import NineSeparatedSubsetSums.Adaptive131Third125
import NineSeparatedSubsetSums.Adaptive131Third126
import NineSeparatedSubsetSums.Adaptive131Third127
import NineSeparatedSubsetSums.Adaptive131Third128
import NineSeparatedSubsetSums.Adaptive131Third129
import NineSeparatedSubsetSums.Adaptive131Third130

namespace NineSeparatedSubsetSums


theorem adaptiveShelf131_no_descending_tail : NoDescendingTail 131 := by
  apply noDescendingTail_of_third_tails 131 109968 max148_second131_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 131 109968 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive131Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive131Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive131Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive131Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive131Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive131Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive131Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive131Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive131Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive131Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive131Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive131Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive131Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive131Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive131Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive131Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive131Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive131Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive131Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive131Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive131Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive131Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive131Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive131Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive131Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive131Third129
  have hlast : b = 130 := by omega
  subst b
  exact adaptive131Third130

#print axioms adaptiveShelf131_no_descending_tail

end NineSeparatedSubsetSums
