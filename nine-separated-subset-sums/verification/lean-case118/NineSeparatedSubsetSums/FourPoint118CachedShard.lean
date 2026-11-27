import NineSeparatedSubsetSums.FourPoint118Checked
import NineSeparatedSubsetSums.CachedThird118Part0
import NineSeparatedSubsetSums.CachedThird118Part1
import NineSeparatedSubsetSums.CachedThird118Part2
import NineSeparatedSubsetSums.CachedThird118Part3
import NineSeparatedSubsetSums.CachedThird118Part4
import NineSeparatedSubsetSums.CachedThird118Single10
import NineSeparatedSubsetSums.CachedThird118Single11

namespace NineSeparatedSubsetSums
theorem cachedFourPoint118_false : cachedSecondShard 118 109014 = false := by
  apply cachedSecondFalse_of_thirds
  intro t ht
  have hc : cachedThirdCount 118 109014 = 12 := by decide +kernel
  rw [hc] at ht
  by_cases h0 : t < 2
  · let o : Fin 2 := ⟨t-0, by omega⟩
    have e : o.val+0=t := by dsimp [o] <;> omega
    rw [←e]
    exact cachedThird118Part0 o
  by_cases h1 : t < 4
  · let o : Fin 2 := ⟨t-2, by omega⟩
    have e : o.val+2=t := by dsimp [o] <;> omega
    rw [←e]
    exact cachedThird118Part1 o
  by_cases h2 : t < 6
  · let o : Fin 2 := ⟨t-4, by omega⟩
    have e : o.val+4=t := by dsimp [o] <;> omega
    rw [←e]
    exact cachedThird118Part2 o
  by_cases h3 : t < 8
  · let o : Fin 2 := ⟨t-6, by omega⟩
    have e : o.val+6=t := by dsimp [o] <;> omega
    rw [←e]
    exact cachedThird118Part3 o
  by_cases h4 : t < 10
  · let o : Fin 2 := ⟨t-8, by omega⟩
    have e : o.val+8=t := by dsimp [o] <;> omega
    rw [←e]
    exact cachedThird118Part4 o
  by_cases h10 : t=10
  · subst t; exact cachedThird118Single10
  · have e : t=11 := by omega
    subst t; exact cachedThird118Single11

theorem fourPoint118_no_descending_tail : NoDescendingTail 118 :=
  noDescendingTail_of_cached 118 109014 max148_second118_fourPoint_moment_bound cachedFourPoint118_false
#print axioms fourPoint118_no_descending_tail
end NineSeparatedSubsetSums
