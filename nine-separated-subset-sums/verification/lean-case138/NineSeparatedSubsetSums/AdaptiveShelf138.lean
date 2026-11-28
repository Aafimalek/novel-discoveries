import NineSeparatedSubsetSums.FourPoint138Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive138Third104
import NineSeparatedSubsetSums.Adaptive138Third105
import NineSeparatedSubsetSums.Adaptive138Third106
import NineSeparatedSubsetSums.Adaptive138Third107
import NineSeparatedSubsetSums.Adaptive138Third108
import NineSeparatedSubsetSums.Adaptive138Third109
import NineSeparatedSubsetSums.Adaptive138Third110
import NineSeparatedSubsetSums.Adaptive138Third111
import NineSeparatedSubsetSums.Adaptive138Third112
import NineSeparatedSubsetSums.Adaptive138Third113
import NineSeparatedSubsetSums.Adaptive138Third114
import NineSeparatedSubsetSums.Adaptive138Third115
import NineSeparatedSubsetSums.Adaptive138Third116
import NineSeparatedSubsetSums.Adaptive138Third117
import NineSeparatedSubsetSums.Adaptive138Third118
import NineSeparatedSubsetSums.Adaptive138Third119
import NineSeparatedSubsetSums.Adaptive138Third120
import NineSeparatedSubsetSums.Adaptive138Third121
import NineSeparatedSubsetSums.Adaptive138Third122
import NineSeparatedSubsetSums.Adaptive138Third123
import NineSeparatedSubsetSums.Adaptive138Third124
import NineSeparatedSubsetSums.Adaptive138Third125
import NineSeparatedSubsetSums.Adaptive138Third126
import NineSeparatedSubsetSums.Adaptive138Third127
import NineSeparatedSubsetSums.Adaptive138Third128
import NineSeparatedSubsetSums.Adaptive138Third129
import NineSeparatedSubsetSums.Adaptive138Third130
import NineSeparatedSubsetSums.Adaptive138Third131
import NineSeparatedSubsetSums.Adaptive138Third132
import NineSeparatedSubsetSums.Adaptive138Third133
import NineSeparatedSubsetSums.Adaptive138Third134
import NineSeparatedSubsetSums.Adaptive138Third135
import NineSeparatedSubsetSums.Adaptive138Third136
import NineSeparatedSubsetSums.Adaptive138Third137

namespace NineSeparatedSubsetSums


theorem adaptiveShelf138_no_descending_tail : NoDescendingTail 138 := by
  apply noDescendingTail_of_third_tails 138 111079 max148_second138_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 138 111079 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive138Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive138Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive138Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive138Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive138Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive138Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive138Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive138Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive138Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive138Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive138Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive138Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive138Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive138Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive138Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive138Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive138Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive138Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive138Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive138Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive138Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive138Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive138Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive138Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive138Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive138Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive138Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive138Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive138Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive138Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive138Third134
  by_cases h135 : b = 135
  · subst b; exact adaptive138Third135
  by_cases h136 : b = 136
  · subst b; exact adaptive138Third136
  have hlast : b = 137 := by omega
  subst b
  exact adaptive138Third137

#print axioms adaptiveShelf138_no_descending_tail

end NineSeparatedSubsetSums
