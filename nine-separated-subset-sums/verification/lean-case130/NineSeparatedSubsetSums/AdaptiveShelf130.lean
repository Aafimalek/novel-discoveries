import NineSeparatedSubsetSums.FourPoint130Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive130Third104
import NineSeparatedSubsetSums.Adaptive130Third105
import NineSeparatedSubsetSums.Adaptive130Third106
import NineSeparatedSubsetSums.Adaptive130Third107
import NineSeparatedSubsetSums.Adaptive130Third108
import NineSeparatedSubsetSums.Adaptive130Third109
import NineSeparatedSubsetSums.Adaptive130Third110
import NineSeparatedSubsetSums.Adaptive130Third111
import NineSeparatedSubsetSums.Adaptive130Third112
import NineSeparatedSubsetSums.Adaptive130Third113
import NineSeparatedSubsetSums.Adaptive130Third114
import NineSeparatedSubsetSums.Adaptive130Third115
import NineSeparatedSubsetSums.Adaptive130Third116
import NineSeparatedSubsetSums.Adaptive130Third117
import NineSeparatedSubsetSums.Adaptive130Third118
import NineSeparatedSubsetSums.Adaptive130Third119
import NineSeparatedSubsetSums.Adaptive130Third120
import NineSeparatedSubsetSums.Adaptive130Third121
import NineSeparatedSubsetSums.Adaptive130Third122
import NineSeparatedSubsetSums.Adaptive130Third123
import NineSeparatedSubsetSums.Adaptive130Third124
import NineSeparatedSubsetSums.Adaptive130Third125
import NineSeparatedSubsetSums.Adaptive130Third126
import NineSeparatedSubsetSums.Adaptive130Third127
import NineSeparatedSubsetSums.Adaptive130Third128
import NineSeparatedSubsetSums.Adaptive130Third129

namespace NineSeparatedSubsetSums


theorem adaptiveShelf130_no_descending_tail : NoDescendingTail 130 := by
  apply noDescendingTail_of_third_tails 130 109846 max148_second130_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 130 109846 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive130Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive130Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive130Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive130Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive130Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive130Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive130Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive130Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive130Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive130Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive130Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive130Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive130Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive130Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive130Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive130Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive130Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive130Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive130Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive130Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive130Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive130Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive130Third126
  by_cases h127 : b = 127
  · subst b; exact adaptive130Third127
  by_cases h128 : b = 128
  · subst b; exact adaptive130Third128
  have hlast : b = 129 := by omega
  subst b
  exact adaptive130Third129

#print axioms adaptiveShelf130_no_descending_tail

end NineSeparatedSubsetSums
