import NineSeparatedSubsetSums.FourPoint141Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive141Third103
import NineSeparatedSubsetSums.Adaptive141Third104
import NineSeparatedSubsetSums.Adaptive141Third105
import NineSeparatedSubsetSums.Adaptive141Third106
import NineSeparatedSubsetSums.Adaptive141Third107
import NineSeparatedSubsetSums.Adaptive141Third108
import NineSeparatedSubsetSums.Adaptive141Third109
import NineSeparatedSubsetSums.Adaptive141Third110
import NineSeparatedSubsetSums.Adaptive141Third111
import NineSeparatedSubsetSums.Adaptive141Third112
import NineSeparatedSubsetSums.Adaptive141Third113
import NineSeparatedSubsetSums.Adaptive141Third114
import NineSeparatedSubsetSums.Adaptive141Third115
import NineSeparatedSubsetSums.Adaptive141Third116
import NineSeparatedSubsetSums.Adaptive141Third117
import NineSeparatedSubsetSums.Adaptive141Third118
import NineSeparatedSubsetSums.Adaptive141Third119
import NineSeparatedSubsetSums.Adaptive141Third120
import NineSeparatedSubsetSums.Adaptive141Third121
import NineSeparatedSubsetSums.Adaptive141Third122
import NineSeparatedSubsetSums.Adaptive141Third123
import NineSeparatedSubsetSums.Adaptive141Third124
import NineSeparatedSubsetSums.Adaptive141Third125
import NineSeparatedSubsetSums.Adaptive141Third126
import NineSeparatedSubsetSums.Adaptive141Third127
import NineSeparatedSubsetSums.Adaptive141Third128
import NineSeparatedSubsetSums.Adaptive141Third129
import NineSeparatedSubsetSums.Adaptive141Third130
import NineSeparatedSubsetSums.Adaptive141Third131
import NineSeparatedSubsetSums.Adaptive141Third132
import NineSeparatedSubsetSums.Adaptive141Third133
import NineSeparatedSubsetSums.Adaptive141Third134
import NineSeparatedSubsetSums.Adaptive141Third135
import NineSeparatedSubsetSums.Adaptive141Third136
import NineSeparatedSubsetSums.Adaptive141Third137
import NineSeparatedSubsetSums.Adaptive141Third138
import NineSeparatedSubsetSums.Adaptive141Third139
import NineSeparatedSubsetSums.Adaptive141Third140

namespace NineSeparatedSubsetSums


theorem adaptiveShelf141_no_descending_tail : NoDescendingTail 141 := by
  apply noDescendingTail_of_third_tails 141 111653 max148_second141_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 141 111653 = 103 := by decide +kernel
  rw [cut] at hlo
  by_cases h103 : b = 103
  · subst b; exact adaptive141Third103
  by_cases h104 : b = 104
  · subst b; exact adaptive141Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive141Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive141Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive141Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive141Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive141Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive141Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive141Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive141Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive141Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive141Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive141Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive141Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive141Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive141Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive141Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive141Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive141Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive141Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive141Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive141Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive141Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive141Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive141Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive141Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive141Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive141Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive141Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive141Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive141Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive141Third134
  by_cases h135 : b = 135
  · subst b; exact adaptive141Third135
  by_cases h136 : b = 136
  · subst b; exact adaptive141Third136
  by_cases h137 : b = 137
  · subst b; exact adaptive141Third137
  by_cases h138 : b = 138
  · subst b; exact adaptive141Third138
  by_cases h139 : b = 139
  · subst b; exact adaptive141Third139
  have hlast : b = 140 := by omega
  subst b
  exact adaptive141Third140

#print axioms adaptiveShelf141_no_descending_tail

end NineSeparatedSubsetSums
