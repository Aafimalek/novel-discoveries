import NineSeparatedSubsetSums.FourPoint117Checked
import NineSeparatedSubsetSums.CachedThird117Part0
import NineSeparatedSubsetSums.CachedThird117Part1
import NineSeparatedSubsetSums.CachedThird117Part2
import NineSeparatedSubsetSums.CachedThird117Part3
import NineSeparatedSubsetSums.CachedThird117Part4
import NineSeparatedSubsetSums.CachedThird117Part5

namespace NineSeparatedSubsetSums
theorem cachedFourPoint117_false : cachedSecondShard 117 109179 = false := by
  apply cachedSecondFalse_of_thirds
  intro t ht
  have hc : cachedThirdCount 117 109179 = 11 := by decide +kernel
  rw [hc] at ht
  by_cases h0 : t < 2
  · let o : Fin 2 := ⟨t-0, by omega⟩
    have e : o.val+0=t := by dsimp [o] <;> omega
    rw [←e]
    exact cachedThird117Part0 o
  by_cases h1 : t < 4
  · let o : Fin 2 := ⟨t-2, by omega⟩
    have e : o.val+2=t := by dsimp [o] <;> omega
    rw [←e]
    exact cachedThird117Part1 o
  by_cases h2 : t < 6
  · let o : Fin 2 := ⟨t-4, by omega⟩
    have e : o.val+4=t := by dsimp [o] <;> omega
    rw [←e]
    exact cachedThird117Part2 o
  by_cases h3 : t < 8
  · let o : Fin 2 := ⟨t-6, by omega⟩
    have e : o.val+6=t := by dsimp [o] <;> omega
    rw [←e]
    exact cachedThird117Part3 o
  by_cases h4 : t < 10
  · let o : Fin 2 := ⟨t-8, by omega⟩
    have e : o.val+8=t := by dsimp [o] <;> omega
    rw [←e]
    exact cachedThird117Part4 o
  let o : Fin 1 := ⟨t-10, by omega⟩
  have e : o.val+10=t := by dsimp [o] <;> omega
  rw [←e]
  exact cachedThird117Part5 o

theorem fourPoint117_no_descending_tail : NoDescendingTail 117 :=
  noDescendingTail_of_cached 117 109179 max148_second117_fourPoint_moment_bound cachedFourPoint117_false
#print axioms fourPoint117_no_descending_tail
end NineSeparatedSubsetSums
