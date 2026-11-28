import NineSeparatedSubsetSums.FourPoint137Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive137Third104
import NineSeparatedSubsetSums.Adaptive137Third105
import NineSeparatedSubsetSums.Adaptive137Third106
import NineSeparatedSubsetSums.Adaptive137Third107
import NineSeparatedSubsetSums.Adaptive137Third108
import NineSeparatedSubsetSums.Adaptive137Third109
import NineSeparatedSubsetSums.Adaptive137Third110
import NineSeparatedSubsetSums.Adaptive137Third111
import NineSeparatedSubsetSums.Adaptive137Third112
import NineSeparatedSubsetSums.Adaptive137Third113
import NineSeparatedSubsetSums.Adaptive137Third114
import NineSeparatedSubsetSums.Adaptive137Third115
import NineSeparatedSubsetSums.Adaptive137Third116
import NineSeparatedSubsetSums.Adaptive137Third117
import NineSeparatedSubsetSums.Adaptive137Third118
import NineSeparatedSubsetSums.Adaptive137Third119
import NineSeparatedSubsetSums.Adaptive137Third120
import NineSeparatedSubsetSums.Adaptive137Third121
import NineSeparatedSubsetSums.Adaptive137Third122
import NineSeparatedSubsetSums.Adaptive137Third123
import NineSeparatedSubsetSums.Adaptive137Third124
import NineSeparatedSubsetSums.Adaptive137Third125
import NineSeparatedSubsetSums.Adaptive137Third126
import NineSeparatedSubsetSums.Adaptive137Third127
import NineSeparatedSubsetSums.Adaptive137Third128
import NineSeparatedSubsetSums.Adaptive137Third129
import NineSeparatedSubsetSums.Adaptive137Third130
import NineSeparatedSubsetSums.Adaptive137Third131
import NineSeparatedSubsetSums.Adaptive137Third132
import NineSeparatedSubsetSums.Adaptive137Third133
import NineSeparatedSubsetSums.Adaptive137Third134
import NineSeparatedSubsetSums.Adaptive137Third135
import NineSeparatedSubsetSums.Adaptive137Third136

namespace NineSeparatedSubsetSums


theorem adaptiveShelf137_no_descending_tail : NoDescendingTail 137 := by
  apply noDescendingTail_of_third_tails 137 111041 max148_second137_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 137 111041 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive137Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive137Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive137Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive137Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive137Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive137Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive137Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive137Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive137Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive137Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive137Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive137Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive137Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive137Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive137Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive137Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive137Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive137Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive137Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive137Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive137Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive137Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive137Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive137Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive137Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive137Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive137Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive137Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive137Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive137Third133
  by_cases h134 : b = 134
  · subst b; exact adaptive137Third134
  by_cases h135 : b = 135
  · subst b; exact adaptive137Third135
  have hlast : b = 136 := by omega
  subst b
  exact adaptive137Third136

#print axioms adaptiveShelf137_no_descending_tail

end NineSeparatedSubsetSums
