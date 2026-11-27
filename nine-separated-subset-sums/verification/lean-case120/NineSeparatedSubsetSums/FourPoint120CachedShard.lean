import NineSeparatedSubsetSums.FourPoint120Checked
import NineSeparatedSubsetSums.EightPoint120_119Shard
import NineSeparatedSubsetSums.FixedThird120Part0
import NineSeparatedSubsetSums.FixedThird120Part1
import NineSeparatedSubsetSums.FixedThird120Part2
import NineSeparatedSubsetSums.FixedThird120Part3
import NineSeparatedSubsetSums.FixedThird120Part4
import NineSeparatedSubsetSums.FixedThird120Part5
import NineSeparatedSubsetSums.FixedThird120Part6

namespace NineSeparatedSubsetSums

theorem fourPoint120_no_descending_tail : NoDescendingTail 120 := by
  apply noDescendingTail_of_third_tails 120 108497 max148_second120_fourPoint_moment_bound
  intro b hlo hhi
  have h0 : cachedThirdLower 120 108497 = 105 := by decide +kernel
  rw [h0] at hlo
  by_cases h120 : b=119
  · subst b
    exact eightPoint120_119_no_descending_tail
  by_cases h118 : b=118
  · subst b
    exact fixedThird120Part6
  have upper : b < 118 := by omega
  apply noDescendingThirdTail_of_cached 120 b 108497
  · intro t ht hd
    exact max148_second120_fourPoint_moment_bound (b::t) (by simp [ht]) hd
  by_cases q0 : b < 112
  · let j : Fin 7 := ⟨b-105, by omega⟩
    have hj : 105+j.val=b := by dsimp [j]; omega
    have ok := fixedThird120Part0 j
    simpa only [hj] using ok
  by_cases q1 : b < 114
  · let j : Fin 2 := ⟨b-112, by omega⟩
    have hj : 112+j.val=b := by dsimp [j]; omega
    have ok := fixedThird120Part1 j
    simpa only [hj] using ok
  by_cases q2 : b < 115
  · let j : Fin 1 := ⟨b-114, by omega⟩
    have hj : 114+j.val=b := by dsimp [j]; omega
    have ok := fixedThird120Part2 j
    simpa only [hj] using ok
  by_cases q3 : b < 116
  · let j : Fin 1 := ⟨b-115, by omega⟩
    have hj : 115+j.val=b := by dsimp [j]; omega
    have ok := fixedThird120Part3 j
    simpa only [hj] using ok
  by_cases q4 : b < 117
  · let j : Fin 1 := ⟨b-116, by omega⟩
    have hj : 116+j.val=b := by dsimp [j]; omega
    have ok := fixedThird120Part4 j
    simpa only [hj] using ok
  let j : Fin 1 := ⟨b-117, by omega⟩
  have hj : 117+j.val=b := by dsimp [j]; omega
  have ok := fixedThird120Part5 j
  simpa only [hj] using ok

#print axioms fourPoint120_no_descending_tail
end NineSeparatedSubsetSums
