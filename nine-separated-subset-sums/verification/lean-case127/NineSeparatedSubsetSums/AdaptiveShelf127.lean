import NineSeparatedSubsetSums.FourPoint127Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive127Third104
import NineSeparatedSubsetSums.Adaptive127Third105
import NineSeparatedSubsetSums.Adaptive127Third106
import NineSeparatedSubsetSums.Adaptive127Third107
import NineSeparatedSubsetSums.Adaptive127Third108
import NineSeparatedSubsetSums.Adaptive127Third109
import NineSeparatedSubsetSums.Adaptive127Third110
import NineSeparatedSubsetSums.Adaptive127Third111
import NineSeparatedSubsetSums.Adaptive127Third112
import NineSeparatedSubsetSums.Adaptive127Third113
import NineSeparatedSubsetSums.Adaptive127Third114
import NineSeparatedSubsetSums.Adaptive127Third115
import NineSeparatedSubsetSums.Adaptive127Third116
import NineSeparatedSubsetSums.Adaptive127Third117
import NineSeparatedSubsetSums.Adaptive127Third118
import NineSeparatedSubsetSums.Adaptive127Third119
import NineSeparatedSubsetSums.Adaptive127Third120
import NineSeparatedSubsetSums.Adaptive127Third121
import NineSeparatedSubsetSums.Adaptive127Third122
import NineSeparatedSubsetSums.Adaptive127Third123
import NineSeparatedSubsetSums.Adaptive127Third124
import NineSeparatedSubsetSums.Adaptive127Third125
import NineSeparatedSubsetSums.Adaptive127Third126

namespace NineSeparatedSubsetSums


theorem adaptiveShelf127_no_descending_tail : NoDescendingTail 127 := by
  apply noDescendingTail_of_third_tails 127 108841 max148_second127_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 127 108841 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive127Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive127Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive127Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive127Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive127Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive127Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive127Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive127Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive127Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive127Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive127Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive127Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive127Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive127Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive127Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive127Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive127Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive127Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive127Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive127Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive127Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive127Third125
  have hlast : b = 126 := by omega
  subst b
  exact adaptive127Third126

#print axioms adaptiveShelf127_no_descending_tail

end NineSeparatedSubsetSums
