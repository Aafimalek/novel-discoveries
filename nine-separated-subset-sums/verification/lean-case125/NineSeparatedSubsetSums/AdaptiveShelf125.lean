import NineSeparatedSubsetSums.FourPoint125Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive125Third105
import NineSeparatedSubsetSums.Adaptive125Third106
import NineSeparatedSubsetSums.Adaptive125Third107
import NineSeparatedSubsetSums.Adaptive125Third108
import NineSeparatedSubsetSums.Adaptive125Third109
import NineSeparatedSubsetSums.Adaptive125Third110
import NineSeparatedSubsetSums.Adaptive125Third111
import NineSeparatedSubsetSums.Adaptive125Third112
import NineSeparatedSubsetSums.Adaptive125Third113
import NineSeparatedSubsetSums.Adaptive125Third114
import NineSeparatedSubsetSums.Adaptive125Third115
import NineSeparatedSubsetSums.Adaptive125Third116
import NineSeparatedSubsetSums.Adaptive125Third117
import NineSeparatedSubsetSums.Adaptive125Third118
import NineSeparatedSubsetSums.Adaptive125Third119
import NineSeparatedSubsetSums.Adaptive125Third120
import NineSeparatedSubsetSums.Adaptive125Third121
import NineSeparatedSubsetSums.Adaptive125Third122
import NineSeparatedSubsetSums.Adaptive125Third123
import NineSeparatedSubsetSums.Adaptive125Third124

namespace NineSeparatedSubsetSums


theorem adaptiveShelf125_no_descending_tail : NoDescendingTail 125 := by
  apply noDescendingTail_of_third_tails 125 109272 max148_second125_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 125 109272 = 105 := by decide +kernel
  rw [cut] at hlo
  by_cases h105 : b = 105
  · subst b; exact adaptive125Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive125Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive125Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive125Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive125Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive125Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive125Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive125Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive125Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive125Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive125Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive125Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive125Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive125Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive125Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive125Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive125Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive125Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive125Third123
  have hlast : b = 124 := by omega
  subst b
  exact adaptive125Third124

#print axioms adaptiveShelf125_no_descending_tail

end NineSeparatedSubsetSums
