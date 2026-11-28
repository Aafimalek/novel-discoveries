import NineSeparatedSubsetSums.FourPoint139Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive139Third104
import NineSeparatedSubsetSums.Adaptive139Third105
import NineSeparatedSubsetSums.Adaptive139Third106
import NineSeparatedSubsetSums.Adaptive139Third107
import NineSeparatedSubsetSums.Adaptive139Third108
import NineSeparatedSubsetSums.Adaptive139Third109
import NineSeparatedSubsetSums.Adaptive139Third110
import NineSeparatedSubsetSums.Adaptive139Third111
import NineSeparatedSubsetSums.Adaptive139Third112
import NineSeparatedSubsetSums.Adaptive139Third113
import NineSeparatedSubsetSums.Adaptive139Third114
import NineSeparatedSubsetSums.Adaptive139Third115
import NineSeparatedSubsetSums.Adaptive139Third116
import NineSeparatedSubsetSums.Adaptive139Third117
import NineSeparatedSubsetSums.Adaptive139Third118
import NineSeparatedSubsetSums.Adaptive139Third119
import NineSeparatedSubsetSums.Adaptive139Third120
import NineSeparatedSubsetSums.Adaptive139Third121
import NineSeparatedSubsetSums.Adaptive139Third122
import NineSeparatedSubsetSums.Adaptive139Third123
import NineSeparatedSubsetSums.Adaptive139Third124
import NineSeparatedSubsetSums.Adaptive139Third125
import NineSeparatedSubsetSums.Adaptive139Third126
import NineSeparatedSubsetSums.Adaptive139Third127
import NineSeparatedSubsetSums.Adaptive139Third128
import NineSeparatedSubsetSums.Adaptive139Third129
import NineSeparatedSubsetSums.Adaptive139Third130
import NineSeparatedSubsetSums.Adaptive139Third131
import NineSeparatedSubsetSums.Adaptive139Third132
import NineSeparatedSubsetSums.Adaptive139Third133
import NineSeparatedSubsetSums.Adaptive139Third134
import NineSeparatedSubsetSums.Adaptive139Third135
import NineSeparatedSubsetSums.Adaptive139Third136
import NineSeparatedSubsetSums.Adaptive139Third137
import NineSeparatedSubsetSums.Adaptive139Third138

namespace NineSeparatedSubsetSums


theorem adaptiveShelf139_no_descending_tail : NoDescendingTail 139 := by
  apply noDescendingTail_of_third_tails 139 111380 max148_second139_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 139 111380 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive139Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive139Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive139Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive139Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive139Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive139Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive139Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive139Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive139Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive139Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive139Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive139Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive139Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive139Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive139Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive139Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive139Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive139Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive139Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive139Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive139Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive139Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive139Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive139Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive139Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive139Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive139Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive139Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive139Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive139Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive139Third134
  by_cases h135 : b = 135
  · subst b; exact adaptive139Third135
  by_cases h136 : b = 136
  · subst b; exact adaptive139Third136
  by_cases h137 : b = 137
  · subst b; exact adaptive139Third137
  have hlast : b = 138 := by omega
  subst b
  exact adaptive139Third138

#print axioms adaptiveShelf139_no_descending_tail

end NineSeparatedSubsetSums
