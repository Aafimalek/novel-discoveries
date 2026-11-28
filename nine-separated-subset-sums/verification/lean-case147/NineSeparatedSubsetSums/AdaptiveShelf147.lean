import NineSeparatedSubsetSums.FourPoint147Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive147Third103
import NineSeparatedSubsetSums.Adaptive147Third104
import NineSeparatedSubsetSums.Adaptive147Third105
import NineSeparatedSubsetSums.Adaptive147Third106
import NineSeparatedSubsetSums.Adaptive147Third107
import NineSeparatedSubsetSums.Adaptive147Third108
import NineSeparatedSubsetSums.Adaptive147Third109
import NineSeparatedSubsetSums.Adaptive147Third110
import NineSeparatedSubsetSums.Adaptive147Third111
import NineSeparatedSubsetSums.Adaptive147Third112
import NineSeparatedSubsetSums.Adaptive147Third113
import NineSeparatedSubsetSums.Adaptive147Third114
import NineSeparatedSubsetSums.Adaptive147Third115
import NineSeparatedSubsetSums.Adaptive147Third116
import NineSeparatedSubsetSums.Adaptive147Third117
import NineSeparatedSubsetSums.Adaptive147Third118
import NineSeparatedSubsetSums.Adaptive147Third119
import NineSeparatedSubsetSums.Adaptive147Third120
import NineSeparatedSubsetSums.Adaptive147Third121
import NineSeparatedSubsetSums.Adaptive147Third122
import NineSeparatedSubsetSums.Adaptive147Third123
import NineSeparatedSubsetSums.Adaptive147Third124
import NineSeparatedSubsetSums.Adaptive147Third125
import NineSeparatedSubsetSums.Adaptive147Third126
import NineSeparatedSubsetSums.Adaptive147Third127
import NineSeparatedSubsetSums.Adaptive147Third128
import NineSeparatedSubsetSums.Adaptive147Third129
import NineSeparatedSubsetSums.Adaptive147Third130
import NineSeparatedSubsetSums.Adaptive147Third131
import NineSeparatedSubsetSums.Adaptive147Third132
import NineSeparatedSubsetSums.Adaptive147Third133
import NineSeparatedSubsetSums.Adaptive147Third134
import NineSeparatedSubsetSums.Adaptive147Third135
import NineSeparatedSubsetSums.Adaptive147Third136
import NineSeparatedSubsetSums.Adaptive147Third137
import NineSeparatedSubsetSums.Adaptive147Third138
import NineSeparatedSubsetSums.Adaptive147Third139
import NineSeparatedSubsetSums.Adaptive147Third140
import NineSeparatedSubsetSums.Adaptive147Third141
import NineSeparatedSubsetSums.Adaptive147Third142
import NineSeparatedSubsetSums.Adaptive147Third143
import NineSeparatedSubsetSums.Adaptive147Third144
import NineSeparatedSubsetSums.Adaptive147Third145
import NineSeparatedSubsetSums.Adaptive147Third146

namespace NineSeparatedSubsetSums


theorem adaptiveShelf147_no_descending_tail : NoDescendingTail 147 := by
  apply noDescendingTail_of_third_tails 147 112835 max148_second147_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 147 112835 = 103 := by decide +kernel
  rw [cut] at hlo
  by_cases h103 : b = 103
  · subst b; exact adaptive147Third103
  by_cases h104 : b = 104
  · subst b; exact adaptive147Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive147Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive147Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive147Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive147Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive147Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive147Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive147Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive147Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive147Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive147Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive147Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive147Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive147Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive147Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive147Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive147Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive147Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive147Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive147Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive147Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive147Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive147Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive147Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive147Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive147Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive147Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive147Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive147Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive147Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive147Third134
  by_cases h135 : b = 135
  · subst b; exact adaptive147Third135
  by_cases h136 : b = 136
  · subst b; exact adaptive147Third136
  by_cases h137 : b = 137
  · subst b; exact adaptive147Third137
  by_cases h138 : b = 138
  · subst b; exact adaptive147Third138
  by_cases h139 : b = 139
  · subst b; exact adaptive147Third139
  by_cases h140 : b = 140
  · subst b; exact adaptive147Third140
  by_cases h141 : b = 141
  · subst b; exact adaptive147Third141
  by_cases h142 : b = 142
  · subst b; exact adaptive147Third142
  by_cases h143 : b = 143
  · subst b; exact adaptive147Third143
  by_cases h144 : b = 144
  · subst b; exact adaptive147Third144
  by_cases h145 : b = 145
  · subst b; exact adaptive147Third145
  have hlast : b = 146 := by omega
  subst b
  exact adaptive147Third146

#print axioms adaptiveShelf147_no_descending_tail

end NineSeparatedSubsetSums
