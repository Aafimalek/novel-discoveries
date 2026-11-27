import NineSeparatedSubsetSums.FourPoint114CachedShard
import NineSeparatedSubsetSums.FourPoint115CachedShard
import NineSeparatedSubsetSums.FourPoint116CachedShard
import NineSeparatedSubsetSums.FourPoint117CachedShard
import NineSeparatedSubsetSums.FourPoint118CachedShard
import NineSeparatedSubsetSums.FourPoint119CachedShard

namespace NineSeparatedSubsetSums

theorem noDescendingTailsThrough119 (a : ℕ) (low : 114 ≤ a) (high : a ≤ 119) :
    NoDescendingTail a := by
  by_cases h114 : a = 114
  · subst a; exact fourPoint114_no_descending_tail
  by_cases h115 : a = 115
  · subst a; exact fourPoint115_no_descending_tail
  by_cases h116 : a = 116
  · subst a; exact fourPoint116_no_descending_tail
  by_cases h117 : a = 117
  · subst a; exact fourPoint117_no_descending_tail
  by_cases h118 : a = 118
  · subst a; exact fourPoint118_no_descending_tail
  have h119 : a = 119 := by omega
  subst a
  exact fourPoint119_no_descending_tail

#print axioms noDescendingTailsThrough119

end NineSeparatedSubsetSums
