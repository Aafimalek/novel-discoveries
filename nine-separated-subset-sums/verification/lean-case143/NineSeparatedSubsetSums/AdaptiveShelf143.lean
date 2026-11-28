import NineSeparatedSubsetSums.FourPoint143Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive143Third103
import NineSeparatedSubsetSums.Adaptive143Third104
import NineSeparatedSubsetSums.Adaptive143Third105
import NineSeparatedSubsetSums.Adaptive143Third106
import NineSeparatedSubsetSums.Adaptive143Third107
import NineSeparatedSubsetSums.Adaptive143Third108
import NineSeparatedSubsetSums.Adaptive143Third109
import NineSeparatedSubsetSums.Adaptive143Third110
import NineSeparatedSubsetSums.Adaptive143Third111
import NineSeparatedSubsetSums.Adaptive143Third112
import NineSeparatedSubsetSums.Adaptive143Third113
import NineSeparatedSubsetSums.Adaptive143Third114
import NineSeparatedSubsetSums.Adaptive143Third115
import NineSeparatedSubsetSums.Adaptive143Third116
import NineSeparatedSubsetSums.Adaptive143Third117
import NineSeparatedSubsetSums.Adaptive143Third118
import NineSeparatedSubsetSums.Adaptive143Third119
import NineSeparatedSubsetSums.Adaptive143Third120
import NineSeparatedSubsetSums.Adaptive143Third121
import NineSeparatedSubsetSums.Adaptive143Third122
import NineSeparatedSubsetSums.Adaptive143Third123
import NineSeparatedSubsetSums.Adaptive143Third124
import NineSeparatedSubsetSums.Adaptive143Third125
import NineSeparatedSubsetSums.Adaptive143Third126
import NineSeparatedSubsetSums.Adaptive143Third127
import NineSeparatedSubsetSums.Adaptive143Third128
import NineSeparatedSubsetSums.Adaptive143Third129
import NineSeparatedSubsetSums.Adaptive143Third130
import NineSeparatedSubsetSums.Adaptive143Third131
import NineSeparatedSubsetSums.Adaptive143Third132
import NineSeparatedSubsetSums.Adaptive143Third133
import NineSeparatedSubsetSums.Adaptive143Third134
import NineSeparatedSubsetSums.Adaptive143Third135
import NineSeparatedSubsetSums.Adaptive143Third136
import NineSeparatedSubsetSums.Adaptive143Third137
import NineSeparatedSubsetSums.Adaptive143Third138
import NineSeparatedSubsetSums.Adaptive143Third139
import NineSeparatedSubsetSums.Adaptive143Third140
import NineSeparatedSubsetSums.Adaptive143Third141
import NineSeparatedSubsetSums.Adaptive143Third142

namespace NineSeparatedSubsetSums


theorem adaptiveShelf143_no_descending_tail : NoDescendingTail 143 := by
  apply noDescendingTail_of_third_tails 143 112040 max148_second143_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 143 112040 = 103 := by decide +kernel
  rw [cut] at hlo
  by_cases h103 : b = 103
  · subst b; exact adaptive143Third103
  by_cases h104 : b = 104
  · subst b; exact adaptive143Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive143Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive143Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive143Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive143Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive143Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive143Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive143Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive143Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive143Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive143Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive143Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive143Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive143Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive143Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive143Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive143Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive143Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive143Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive143Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive143Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive143Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive143Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive143Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive143Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive143Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive143Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive143Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive143Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive143Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive143Third134
  by_cases h135 : b = 135
  · subst b; exact adaptive143Third135
  by_cases h136 : b = 136
  · subst b; exact adaptive143Third136
  by_cases h137 : b = 137
  · subst b; exact adaptive143Third137
  by_cases h138 : b = 138
  · subst b; exact adaptive143Third138
  by_cases h139 : b = 139
  · subst b; exact adaptive143Third139
  by_cases h140 : b = 140
  · subst b; exact adaptive143Third140
  by_cases h141 : b = 141
  · subst b; exact adaptive143Third141
  have hlast : b = 142 := by omega
  subst b
  exact adaptive143Third142

#print axioms adaptiveShelf143_no_descending_tail

end NineSeparatedSubsetSums
