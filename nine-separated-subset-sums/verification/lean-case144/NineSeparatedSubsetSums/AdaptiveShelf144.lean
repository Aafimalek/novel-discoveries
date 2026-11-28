import NineSeparatedSubsetSums.FourPoint144Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive144Third103
import NineSeparatedSubsetSums.Adaptive144Third104
import NineSeparatedSubsetSums.Adaptive144Third105
import NineSeparatedSubsetSums.Adaptive144Third106
import NineSeparatedSubsetSums.Adaptive144Third107
import NineSeparatedSubsetSums.Adaptive144Third108
import NineSeparatedSubsetSums.Adaptive144Third109
import NineSeparatedSubsetSums.Adaptive144Third110
import NineSeparatedSubsetSums.Adaptive144Third111
import NineSeparatedSubsetSums.Adaptive144Third112
import NineSeparatedSubsetSums.Adaptive144Third113
import NineSeparatedSubsetSums.Adaptive144Third114
import NineSeparatedSubsetSums.Adaptive144Third115
import NineSeparatedSubsetSums.Adaptive144Third116
import NineSeparatedSubsetSums.Adaptive144Third117
import NineSeparatedSubsetSums.Adaptive144Third118
import NineSeparatedSubsetSums.Adaptive144Third119
import NineSeparatedSubsetSums.Adaptive144Third120
import NineSeparatedSubsetSums.Adaptive144Third121
import NineSeparatedSubsetSums.Adaptive144Third122
import NineSeparatedSubsetSums.Adaptive144Third123
import NineSeparatedSubsetSums.Adaptive144Third124
import NineSeparatedSubsetSums.Adaptive144Third125
import NineSeparatedSubsetSums.Adaptive144Third126
import NineSeparatedSubsetSums.Adaptive144Third127
import NineSeparatedSubsetSums.Adaptive144Third128
import NineSeparatedSubsetSums.Adaptive144Third129
import NineSeparatedSubsetSums.Adaptive144Third130
import NineSeparatedSubsetSums.Adaptive144Third131
import NineSeparatedSubsetSums.Adaptive144Third132
import NineSeparatedSubsetSums.Adaptive144Third133
import NineSeparatedSubsetSums.Adaptive144Third134
import NineSeparatedSubsetSums.Adaptive144Third135
import NineSeparatedSubsetSums.Adaptive144Third136
import NineSeparatedSubsetSums.Adaptive144Third137
import NineSeparatedSubsetSums.Adaptive144Third138
import NineSeparatedSubsetSums.Adaptive144Third139
import NineSeparatedSubsetSums.Adaptive144Third140
import NineSeparatedSubsetSums.Adaptive144Third141
import NineSeparatedSubsetSums.Adaptive144Third142
import NineSeparatedSubsetSums.Adaptive144Third143

namespace NineSeparatedSubsetSums


theorem adaptiveShelf144_no_descending_tail : NoDescendingTail 144 := by
  apply noDescendingTail_of_third_tails 144 112221 max148_second144_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 144 112221 = 103 := by decide +kernel
  rw [cut] at hlo
  by_cases h103 : b = 103
  · subst b; exact adaptive144Third103
  by_cases h104 : b = 104
  · subst b; exact adaptive144Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive144Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive144Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive144Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive144Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive144Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive144Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive144Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive144Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive144Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive144Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive144Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive144Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive144Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive144Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive144Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive144Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive144Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive144Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive144Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive144Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive144Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive144Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive144Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive144Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive144Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive144Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive144Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive144Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive144Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive144Third134
  by_cases h135 : b = 135
  · subst b; exact adaptive144Third135
  by_cases h136 : b = 136
  · subst b; exact adaptive144Third136
  by_cases h137 : b = 137
  · subst b; exact adaptive144Third137
  by_cases h138 : b = 138
  · subst b; exact adaptive144Third138
  by_cases h139 : b = 139
  · subst b; exact adaptive144Third139
  by_cases h140 : b = 140
  · subst b; exact adaptive144Third140
  by_cases h141 : b = 141
  · subst b; exact adaptive144Third141
  by_cases h142 : b = 142
  · subst b; exact adaptive144Third142
  have hlast : b = 143 := by omega
  subst b
  exact adaptive144Third143

#print axioms adaptiveShelf144_no_descending_tail

end NineSeparatedSubsetSums
