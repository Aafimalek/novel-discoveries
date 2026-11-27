import NineSeparatedSubsetSums.FourPoint124Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive124Third105
import NineSeparatedSubsetSums.Adaptive124Third106
import NineSeparatedSubsetSums.Adaptive124Third107
import NineSeparatedSubsetSums.Adaptive124Third108
import NineSeparatedSubsetSums.Adaptive124Third109
import NineSeparatedSubsetSums.Adaptive124Third110
import NineSeparatedSubsetSums.Adaptive124Third111
import NineSeparatedSubsetSums.Adaptive124Third112
import NineSeparatedSubsetSums.Adaptive124Third113
import NineSeparatedSubsetSums.Adaptive124Third114
import NineSeparatedSubsetSums.Adaptive124Third115
import NineSeparatedSubsetSums.Adaptive124Third116
import NineSeparatedSubsetSums.Adaptive124Third117
import NineSeparatedSubsetSums.Adaptive124Third118
import NineSeparatedSubsetSums.Adaptive124Third119
import NineSeparatedSubsetSums.Adaptive124Third120
import NineSeparatedSubsetSums.Adaptive124Third121
import NineSeparatedSubsetSums.Adaptive124Third122
import NineSeparatedSubsetSums.Adaptive124Third123

namespace NineSeparatedSubsetSums


theorem adaptiveShelf124_no_descending_tail : NoDescendingTail 124 := by
  apply noDescendingTail_of_third_tails 124 109260 max148_second124_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 124 109260 = 105 := by decide +kernel
  rw [cut] at hlo
  by_cases h105 : b = 105
  · subst b; exact adaptive124Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive124Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive124Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive124Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive124Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive124Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive124Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive124Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive124Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive124Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive124Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive124Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive124Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive124Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive124Third119
  by_cases h120 : b = 120
  · subst b; exact adaptive124Third120
  by_cases h121 : b = 121
  · subst b; exact adaptive124Third121
  by_cases h122 : b = 122
  · subst b; exact adaptive124Third122
  have hlast : b = 123 := by omega
  subst b
  exact adaptive124Third123

#print axioms adaptiveShelf124_no_descending_tail

end NineSeparatedSubsetSums
