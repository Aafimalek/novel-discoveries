import NineSeparatedSubsetSums.FourPoint121Checked
import NineSeparatedSubsetSums.CachedFixedThird
import NineSeparatedSubsetSums.Adaptive121Third105
import NineSeparatedSubsetSums.Adaptive121Third106
import NineSeparatedSubsetSums.Adaptive121Third107
import NineSeparatedSubsetSums.Adaptive121Third108
import NineSeparatedSubsetSums.Adaptive121Third109
import NineSeparatedSubsetSums.Adaptive121Third110
import NineSeparatedSubsetSums.Adaptive121Third111
import NineSeparatedSubsetSums.Adaptive121Third112
import NineSeparatedSubsetSums.Adaptive121Third113
import NineSeparatedSubsetSums.Adaptive121Third114
import NineSeparatedSubsetSums.Adaptive121Third115
import NineSeparatedSubsetSums.Adaptive121Third116
import NineSeparatedSubsetSums.Adaptive121Third117
import NineSeparatedSubsetSums.Adaptive121Third118
import NineSeparatedSubsetSums.Adaptive121Third119
import NineSeparatedSubsetSums.Adaptive121Third120

namespace NineSeparatedSubsetSums


theorem adaptiveShelf121_no_descending_tail : NoDescendingTail 121 := by
  apply noDescendingTail_of_third_tails 121 108868 max148_second121_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower 121 108868 = 105 := by decide +kernel
  rw [cut] at hlo
  by_cases h105 : b = 105
  · subst b; exact adaptive121Third105
  by_cases h106 : b = 106
  · subst b; exact adaptive121Third106
  by_cases h107 : b = 107
  · subst b; exact adaptive121Third107
  by_cases h108 : b = 108
  · subst b; exact adaptive121Third108
  by_cases h109 : b = 109
  · subst b; exact adaptive121Third109
  by_cases h110 : b = 110
  · subst b; exact adaptive121Third110
  by_cases h111 : b = 111
  · subst b; exact adaptive121Third111
  by_cases h112 : b = 112
  · subst b; exact adaptive121Third112
  by_cases h113 : b = 113
  · subst b; exact adaptive121Third113
  by_cases h114 : b = 114
  · subst b; exact adaptive121Third114
  by_cases h115 : b = 115
  · subst b; exact adaptive121Third115
  by_cases h116 : b = 116
  · subst b; exact adaptive121Third116
  by_cases h117 : b = 117
  · subst b; exact adaptive121Third117
  by_cases h118 : b = 118
  · subst b; exact adaptive121Third118
  by_cases h119 : b = 119
  · subst b; exact adaptive121Third119
  have hlast : b = 120 := by omega
  subst b
  exact adaptive121Third120

#print axioms adaptiveShelf121_no_descending_tail

end NineSeparatedSubsetSums
