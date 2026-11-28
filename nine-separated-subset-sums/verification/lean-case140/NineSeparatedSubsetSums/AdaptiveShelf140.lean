import NineSeparatedSubsetSums.FourPoint140Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive140Third104
import NineSeparatedSubsetSums.Adaptive140Third105
import NineSeparatedSubsetSums.Adaptive140Third106
import NineSeparatedSubsetSums.Adaptive140Third107
import NineSeparatedSubsetSums.Adaptive140Third108
import NineSeparatedSubsetSums.Adaptive140Third109
import NineSeparatedSubsetSums.Adaptive140Third110
import NineSeparatedSubsetSums.Adaptive140Third111
import NineSeparatedSubsetSums.Adaptive140Third112
import NineSeparatedSubsetSums.Adaptive140Third113
import NineSeparatedSubsetSums.Adaptive140Third114
import NineSeparatedSubsetSums.Adaptive140Third115
import NineSeparatedSubsetSums.Adaptive140Third116
import NineSeparatedSubsetSums.Adaptive140Third117
import NineSeparatedSubsetSums.Adaptive140Third118
import NineSeparatedSubsetSums.Adaptive140Third119
import NineSeparatedSubsetSums.Adaptive140Third120
import NineSeparatedSubsetSums.Adaptive140Third121
import NineSeparatedSubsetSums.Adaptive140Third122
import NineSeparatedSubsetSums.Adaptive140Third123
import NineSeparatedSubsetSums.Adaptive140Third124
import NineSeparatedSubsetSums.Adaptive140Third125
import NineSeparatedSubsetSums.Adaptive140Third126
import NineSeparatedSubsetSums.Adaptive140Third127
import NineSeparatedSubsetSums.Adaptive140Third128
import NineSeparatedSubsetSums.Adaptive140Third129
import NineSeparatedSubsetSums.Adaptive140Third130
import NineSeparatedSubsetSums.Adaptive140Third131
import NineSeparatedSubsetSums.Adaptive140Third132
import NineSeparatedSubsetSums.Adaptive140Third133
import NineSeparatedSubsetSums.Adaptive140Third134
import NineSeparatedSubsetSums.Adaptive140Third135
import NineSeparatedSubsetSums.Adaptive140Third136
import NineSeparatedSubsetSums.Adaptive140Third137
import NineSeparatedSubsetSums.Adaptive140Third138
import NineSeparatedSubsetSums.Adaptive140Third139

namespace NineSeparatedSubsetSums


theorem adaptiveShelf140_no_descending_tail : NoDescendingTail 140 := by
  apply noDescendingTail_of_third_tails 140 111588 max148_second140_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 140 111588 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive140Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive140Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive140Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive140Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive140Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive140Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive140Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive140Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive140Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive140Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive140Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive140Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive140Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive140Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive140Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive140Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive140Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive140Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive140Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive140Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive140Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive140Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive140Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive140Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive140Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive140Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive140Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive140Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive140Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive140Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive140Third134
  by_cases h135 : b = 135
  · subst b; exact adaptive140Third135
  by_cases h136 : b = 136
  · subst b; exact adaptive140Third136
  by_cases h137 : b = 137
  · subst b; exact adaptive140Third137
  by_cases h138 : b = 138
  · subst b; exact adaptive140Third138
  have hlast : b = 139 := by omega
  subst b
  exact adaptive140Third139

#print axioms adaptiveShelf140_no_descending_tail

end NineSeparatedSubsetSums
