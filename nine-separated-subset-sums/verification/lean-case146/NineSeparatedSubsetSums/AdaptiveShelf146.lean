import NineSeparatedSubsetSums.FourPoint146Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive146Third103
import NineSeparatedSubsetSums.Adaptive146Third104
import NineSeparatedSubsetSums.Adaptive146Third105
import NineSeparatedSubsetSums.Adaptive146Third106
import NineSeparatedSubsetSums.Adaptive146Third107
import NineSeparatedSubsetSums.Adaptive146Third108
import NineSeparatedSubsetSums.Adaptive146Third109
import NineSeparatedSubsetSums.Adaptive146Third110
import NineSeparatedSubsetSums.Adaptive146Third111
import NineSeparatedSubsetSums.Adaptive146Third112
import NineSeparatedSubsetSums.Adaptive146Third113
import NineSeparatedSubsetSums.Adaptive146Third114
import NineSeparatedSubsetSums.Adaptive146Third115
import NineSeparatedSubsetSums.Adaptive146Third116
import NineSeparatedSubsetSums.Adaptive146Third117
import NineSeparatedSubsetSums.Adaptive146Third118
import NineSeparatedSubsetSums.Adaptive146Third119
import NineSeparatedSubsetSums.Adaptive146Third120
import NineSeparatedSubsetSums.Adaptive146Third121
import NineSeparatedSubsetSums.Adaptive146Third122
import NineSeparatedSubsetSums.Adaptive146Third123
import NineSeparatedSubsetSums.Adaptive146Third124
import NineSeparatedSubsetSums.Adaptive146Third125
import NineSeparatedSubsetSums.Adaptive146Third126
import NineSeparatedSubsetSums.Adaptive146Third127
import NineSeparatedSubsetSums.Adaptive146Third128
import NineSeparatedSubsetSums.Adaptive146Third129
import NineSeparatedSubsetSums.Adaptive146Third130
import NineSeparatedSubsetSums.Adaptive146Third131
import NineSeparatedSubsetSums.Adaptive146Third132
import NineSeparatedSubsetSums.Adaptive146Third133
import NineSeparatedSubsetSums.Adaptive146Third134
import NineSeparatedSubsetSums.Adaptive146Third135
import NineSeparatedSubsetSums.Adaptive146Third136
import NineSeparatedSubsetSums.Adaptive146Third137
import NineSeparatedSubsetSums.Adaptive146Third138
import NineSeparatedSubsetSums.Adaptive146Third139
import NineSeparatedSubsetSums.Adaptive146Third140
import NineSeparatedSubsetSums.Adaptive146Third141
import NineSeparatedSubsetSums.Adaptive146Third142
import NineSeparatedSubsetSums.Adaptive146Third143
import NineSeparatedSubsetSums.Adaptive146Third144
import NineSeparatedSubsetSums.Adaptive146Third145

namespace NineSeparatedSubsetSums


theorem adaptiveShelf146_no_descending_tail : NoDescendingTail 146 := by
  apply noDescendingTail_of_third_tails 146 112631 max148_second146_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 146 112631 = 103 := by decide +kernel
  rw [cut] at hlo
  by_cases h103 : b = 103
  · subst b; exact adaptive146Third103
  by_cases h104 : b = 104
  · subst b; exact adaptive146Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive146Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive146Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive146Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive146Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive146Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive146Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive146Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive146Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive146Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive146Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive146Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive146Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive146Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive146Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive146Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive146Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive146Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive146Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive146Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive146Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive146Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive146Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive146Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive146Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive146Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive146Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive146Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive146Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive146Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive146Third134
  by_cases h135 : b = 135
  · subst b; exact adaptive146Third135
  by_cases h136 : b = 136
  · subst b; exact adaptive146Third136
  by_cases h137 : b = 137
  · subst b; exact adaptive146Third137
  by_cases h138 : b = 138
  · subst b; exact adaptive146Third138
  by_cases h139 : b = 139
  · subst b; exact adaptive146Third139
  by_cases h140 : b = 140
  · subst b; exact adaptive146Third140
  by_cases h141 : b = 141
  · subst b; exact adaptive146Third141
  by_cases h142 : b = 142
  · subst b; exact adaptive146Third142
  by_cases h143 : b = 143
  · subst b; exact adaptive146Third143
  by_cases h144 : b = 144
  · subst b; exact adaptive146Third144
  have hlast : b = 145 := by omega
  subst b
  exact adaptive146Third145

#print axioms adaptiveShelf146_no_descending_tail

end NineSeparatedSubsetSums
