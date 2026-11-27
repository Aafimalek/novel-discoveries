import NineSeparatedSubsetSums.FourPoint122Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive122Third105
import NineSeparatedSubsetSums.Adaptive122Third106
import NineSeparatedSubsetSums.Adaptive122Third107
import NineSeparatedSubsetSums.Adaptive122Third108
import NineSeparatedSubsetSums.Adaptive122Third109
import NineSeparatedSubsetSums.Adaptive122Third110
import NineSeparatedSubsetSums.Adaptive122Third111
import NineSeparatedSubsetSums.Adaptive122Third112
import NineSeparatedSubsetSums.Adaptive122Third113
import NineSeparatedSubsetSums.Adaptive122Third114
import NineSeparatedSubsetSums.Adaptive122Third115
import NineSeparatedSubsetSums.Adaptive122Third116
import NineSeparatedSubsetSums.Adaptive122Third117
import NineSeparatedSubsetSums.Adaptive122Third118
import NineSeparatedSubsetSums.Adaptive122Third119
import NineSeparatedSubsetSums.Adaptive122Third120
import NineSeparatedSubsetSums.Adaptive122Third121

namespace NineSeparatedSubsetSums


theorem adaptiveShelf122_no_descending_tail : NoDescendingTail 122 := by
  apply noDescendingTail_of_third_tails 122 109064 max148_second122_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 122 109064 = 105 := by decide +kernel
  rw [cut] at hlo
  by_cases h105 : b = 105
  · subst b; exact adaptive122Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive122Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive122Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive122Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive122Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive122Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive122Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive122Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive122Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive122Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive122Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive122Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive122Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive122Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive122Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive122Third120
  have hlast : b = 121 := by omega
  subst b
  exact adaptive122Third121

#print axioms adaptiveShelf122_no_descending_tail

end NineSeparatedSubsetSums
