import NineSeparatedSubsetSums.FourPoint136Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive136Third104
import NineSeparatedSubsetSums.Adaptive136Third105
import NineSeparatedSubsetSums.Adaptive136Third106
import NineSeparatedSubsetSums.Adaptive136Third107
import NineSeparatedSubsetSums.Adaptive136Third108
import NineSeparatedSubsetSums.Adaptive136Third109
import NineSeparatedSubsetSums.Adaptive136Third110
import NineSeparatedSubsetSums.Adaptive136Third111
import NineSeparatedSubsetSums.Adaptive136Third112
import NineSeparatedSubsetSums.Adaptive136Third113
import NineSeparatedSubsetSums.Adaptive136Third114
import NineSeparatedSubsetSums.Adaptive136Third115
import NineSeparatedSubsetSums.Adaptive136Third116
import NineSeparatedSubsetSums.Adaptive136Third117
import NineSeparatedSubsetSums.Adaptive136Third118
import NineSeparatedSubsetSums.Adaptive136Third119
import NineSeparatedSubsetSums.Adaptive136Third120
import NineSeparatedSubsetSums.Adaptive136Third121
import NineSeparatedSubsetSums.Adaptive136Third122
import NineSeparatedSubsetSums.Adaptive136Third123
import NineSeparatedSubsetSums.Adaptive136Third124
import NineSeparatedSubsetSums.Adaptive136Third125
import NineSeparatedSubsetSums.Adaptive136Third126
import NineSeparatedSubsetSums.Adaptive136Third127
import NineSeparatedSubsetSums.Adaptive136Third128
import NineSeparatedSubsetSums.Adaptive136Third129
import NineSeparatedSubsetSums.Adaptive136Third130
import NineSeparatedSubsetSums.Adaptive136Third131
import NineSeparatedSubsetSums.Adaptive136Third132
import NineSeparatedSubsetSums.Adaptive136Third133
import NineSeparatedSubsetSums.Adaptive136Third134
import NineSeparatedSubsetSums.Adaptive136Third135

namespace NineSeparatedSubsetSums


theorem adaptiveShelf136_no_descending_tail : NoDescendingTail 136 := by
  apply noDescendingTail_of_third_tails 136 110825 max148_second136_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 136 110825 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive136Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive136Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive136Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive136Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive136Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive136Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive136Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive136Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive136Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive136Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive136Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive136Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive136Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive136Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive136Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive136Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive136Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive136Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive136Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive136Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive136Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive136Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive136Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive136Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive136Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive136Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive136Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive136Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive136Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive136Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive136Third134
  have hlast : b = 135 := by omega
  subst b
  exact adaptive136Third135

#print axioms adaptiveShelf136_no_descending_tail

end NineSeparatedSubsetSums
