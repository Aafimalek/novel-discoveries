import NineSeparatedSubsetSums.FourPoint142Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive142Third103
import NineSeparatedSubsetSums.Adaptive142Third104
import NineSeparatedSubsetSums.Adaptive142Third105
import NineSeparatedSubsetSums.Adaptive142Third106
import NineSeparatedSubsetSums.Adaptive142Third107
import NineSeparatedSubsetSums.Adaptive142Third108
import NineSeparatedSubsetSums.Adaptive142Third109
import NineSeparatedSubsetSums.Adaptive142Third110
import NineSeparatedSubsetSums.Adaptive142Third111
import NineSeparatedSubsetSums.Adaptive142Third112
import NineSeparatedSubsetSums.Adaptive142Third113
import NineSeparatedSubsetSums.Adaptive142Third114
import NineSeparatedSubsetSums.Adaptive142Third115
import NineSeparatedSubsetSums.Adaptive142Third116
import NineSeparatedSubsetSums.Adaptive142Third117
import NineSeparatedSubsetSums.Adaptive142Third118
import NineSeparatedSubsetSums.Adaptive142Third119
import NineSeparatedSubsetSums.Adaptive142Third120
import NineSeparatedSubsetSums.Adaptive142Third121
import NineSeparatedSubsetSums.Adaptive142Third122
import NineSeparatedSubsetSums.Adaptive142Third123
import NineSeparatedSubsetSums.Adaptive142Third124
import NineSeparatedSubsetSums.Adaptive142Third125
import NineSeparatedSubsetSums.Adaptive142Third126
import NineSeparatedSubsetSums.Adaptive142Third127
import NineSeparatedSubsetSums.Adaptive142Third128
import NineSeparatedSubsetSums.Adaptive142Third129
import NineSeparatedSubsetSums.Adaptive142Third130
import NineSeparatedSubsetSums.Adaptive142Third131
import NineSeparatedSubsetSums.Adaptive142Third132
import NineSeparatedSubsetSums.Adaptive142Third133
import NineSeparatedSubsetSums.Adaptive142Third134
import NineSeparatedSubsetSums.Adaptive142Third135
import NineSeparatedSubsetSums.Adaptive142Third136
import NineSeparatedSubsetSums.Adaptive142Third137
import NineSeparatedSubsetSums.Adaptive142Third138
import NineSeparatedSubsetSums.Adaptive142Third139
import NineSeparatedSubsetSums.Adaptive142Third140
import NineSeparatedSubsetSums.Adaptive142Third141

namespace NineSeparatedSubsetSums


theorem adaptiveShelf142_no_descending_tail : NoDescendingTail 142 := by
  apply noDescendingTail_of_third_tails 142 111874 max148_second142_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 142 111874 = 103 := by decide +kernel
  rw [cut] at hlo
  by_cases h103 : b = 103
  · subst b; exact adaptive142Third103
  by_cases h104 : b = 104
  · subst b; exact adaptive142Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive142Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive142Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive142Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive142Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive142Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive142Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive142Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive142Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive142Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive142Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive142Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive142Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive142Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive142Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive142Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive142Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive142Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive142Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive142Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive142Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive142Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive142Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive142Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive142Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive142Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive142Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive142Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive142Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive142Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive142Third134
  by_cases h135 : b = 135
  · subst b; exact adaptive142Third135
  by_cases h136 : b = 136
  · subst b; exact adaptive142Third136
  by_cases h137 : b = 137
  · subst b; exact adaptive142Third137
  by_cases h138 : b = 138
  · subst b; exact adaptive142Third138
  by_cases h139 : b = 139
  · subst b; exact adaptive142Third139
  by_cases h140 : b = 140
  · subst b; exact adaptive142Third140
  have hlast : b = 141 := by omega
  subst b
  exact adaptive142Third141

#print axioms adaptiveShelf142_no_descending_tail

end NineSeparatedSubsetSums
