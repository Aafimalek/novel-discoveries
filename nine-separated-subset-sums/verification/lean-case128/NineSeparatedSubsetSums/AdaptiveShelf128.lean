import NineSeparatedSubsetSums.FourPoint128Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive128Third104
import NineSeparatedSubsetSums.Adaptive128Third105
import NineSeparatedSubsetSums.Adaptive128Third106
import NineSeparatedSubsetSums.Adaptive128Third107
import NineSeparatedSubsetSums.Adaptive128Third108
import NineSeparatedSubsetSums.Adaptive128Third109
import NineSeparatedSubsetSums.Adaptive128Third110
import NineSeparatedSubsetSums.Adaptive128Third111
import NineSeparatedSubsetSums.Adaptive128Third112
import NineSeparatedSubsetSums.Adaptive128Third113
import NineSeparatedSubsetSums.Adaptive128Third114
import NineSeparatedSubsetSums.Adaptive128Third115
import NineSeparatedSubsetSums.Adaptive128Third116
import NineSeparatedSubsetSums.Adaptive128Third117
import NineSeparatedSubsetSums.Adaptive128Third118
import NineSeparatedSubsetSums.Adaptive128Third119
import NineSeparatedSubsetSums.Adaptive128Third120
import NineSeparatedSubsetSums.Adaptive128Third121
import NineSeparatedSubsetSums.Adaptive128Third122
import NineSeparatedSubsetSums.Adaptive128Third123
import NineSeparatedSubsetSums.Adaptive128Third124
import NineSeparatedSubsetSums.Adaptive128Third125
import NineSeparatedSubsetSums.Adaptive128Third126
import NineSeparatedSubsetSums.Adaptive128Third127

namespace NineSeparatedSubsetSums


theorem adaptiveShelf128_no_descending_tail : NoDescendingTail 128 := by
  apply noDescendingTail_of_third_tails 128 109269 max148_second128_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 128 109269 = 104 := by decide +kernel
  rw [cut] at hlo
  by_cases h104 : b = 104
  · subst b; exact adaptive128Third104
  by_cases h105 : b = 105
  · subst b; exact adaptive128Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive128Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive128Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive128Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive128Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive128Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive128Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive128Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive128Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive128Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive128Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive128Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive128Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive128Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive128Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive128Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive128Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive128Third122
  by_cases h123 : b = 123
  · subst b; exact adaptive128Third123
  by_cases h124 : b = 124
  · subst b; exact adaptive128Third124
  by_cases h125 : b = 125
  · subst b; exact adaptive128Third125
  by_cases h126 : b = 126
  · subst b; exact adaptive128Third126
  have hlast : b = 127 := by omega
  subst b
  exact adaptive128Third127

#print axioms adaptiveShelf128_no_descending_tail

end NineSeparatedSubsetSums
