import NineSeparatedSubsetSums.FourPoint135Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive135Third104
import NineSeparatedSubsetSums.Adaptive135Third105
import NineSeparatedSubsetSums.Adaptive135Third106
import NineSeparatedSubsetSums.Adaptive135Third107
import NineSeparatedSubsetSums.Adaptive135Third108
import NineSeparatedSubsetSums.Adaptive135Third109
import NineSeparatedSubsetSums.Adaptive135Third110
import NineSeparatedSubsetSums.Adaptive135Third111
import NineSeparatedSubsetSums.Adaptive135Third112
import NineSeparatedSubsetSums.Adaptive135Third113
import NineSeparatedSubsetSums.Adaptive135Third114
import NineSeparatedSubsetSums.Adaptive135Third115
import NineSeparatedSubsetSums.Adaptive135Third116
import NineSeparatedSubsetSums.Adaptive135Third117
import NineSeparatedSubsetSums.Adaptive135Third118
import NineSeparatedSubsetSums.Adaptive135Third119
import NineSeparatedSubsetSums.Adaptive135Third120
import NineSeparatedSubsetSums.Adaptive135Third121
import NineSeparatedSubsetSums.Adaptive135Third122
import NineSeparatedSubsetSums.Adaptive135Third123
import NineSeparatedSubsetSums.Adaptive135Third124
import NineSeparatedSubsetSums.Adaptive135Third125
import NineSeparatedSubsetSums.Adaptive135Third126
import NineSeparatedSubsetSums.Adaptive135Third127
import NineSeparatedSubsetSums.Adaptive135Third128
import NineSeparatedSubsetSums.Adaptive135Third129
import NineSeparatedSubsetSums.Adaptive135Third130
import NineSeparatedSubsetSums.Adaptive135Third131
import NineSeparatedSubsetSums.Adaptive135Third132
import NineSeparatedSubsetSums.Adaptive135Third133
import NineSeparatedSubsetSums.Adaptive135Third134

namespace NineSeparatedSubsetSums


theorem adaptiveShelf135_no_descending_tail : NoDescendingTail 135 := by
  apply noDescendingTail_of_third_tails 135 110858 max148_second135_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 135 110858 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive135Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive135Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive135Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive135Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive135Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive135Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive135Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive135Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive135Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive135Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive135Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive135Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive135Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive135Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive135Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive135Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive135Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive135Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive135Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive135Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive135Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive135Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive135Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive135Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive135Third128
  by_cases h129 : b = 129
  · subst b; exact adaptive135Third129
  by_cases h130 : b = 130
  · subst b; exact adaptive135Third130
  by_cases h131 : b = 131
  · subst b; exact adaptive135Third131
  by_cases h132 : b = 132
  · subst b; exact adaptive135Third132
  by_cases h133 : b = 133
  · subst b; exact adaptive135Third133
  have hlast : b = 134 := by omega
  subst b
  exact adaptive135Third134

#print axioms adaptiveShelf135_no_descending_tail

end NineSeparatedSubsetSums
