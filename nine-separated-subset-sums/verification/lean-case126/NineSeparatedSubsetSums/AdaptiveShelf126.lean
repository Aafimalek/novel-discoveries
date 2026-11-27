import NineSeparatedSubsetSums.FourPoint126Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive126Third105
import NineSeparatedSubsetSums.Adaptive126Third106
import NineSeparatedSubsetSums.Adaptive126Third107
import NineSeparatedSubsetSums.Adaptive126Third108
import NineSeparatedSubsetSums.Adaptive126Third109
import NineSeparatedSubsetSums.Adaptive126Third110
import NineSeparatedSubsetSums.Adaptive126Third111
import NineSeparatedSubsetSums.Adaptive126Third112
import NineSeparatedSubsetSums.Adaptive126Third113
import NineSeparatedSubsetSums.Adaptive126Third114
import NineSeparatedSubsetSums.Adaptive126Third115
import NineSeparatedSubsetSums.Adaptive126Third116
import NineSeparatedSubsetSums.Adaptive126Third117
import NineSeparatedSubsetSums.Adaptive126Third118
import NineSeparatedSubsetSums.Adaptive126Third119
import NineSeparatedSubsetSums.Adaptive126Third120
import NineSeparatedSubsetSums.Adaptive126Third121
import NineSeparatedSubsetSums.Adaptive126Third122
import NineSeparatedSubsetSums.Adaptive126Third123
import NineSeparatedSubsetSums.Adaptive126Third124
import NineSeparatedSubsetSums.Adaptive126Third125

namespace NineSeparatedSubsetSums


theorem adaptiveShelf126_no_descending_tail : NoDescendingTail 126 := by
  apply noDescendingTail_of_third_tails 126 109252 max148_second126_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 126 109252 = 105 := by decide +kernel
  rw [cut] at hlo
  by_cases h105 : b = 105
  · subst b; exact adaptive126Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive126Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive126Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive126Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive126Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive126Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive126Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive126Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive126Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive126Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive126Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive126Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive126Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive126Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive126Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive126Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive126Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive126Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive126Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive126Third124
  have hlast : b = 125 := by omega
  subst b
  exact adaptive126Third125

#print axioms adaptiveShelf126_no_descending_tail

end NineSeparatedSubsetSums
