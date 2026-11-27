import NineSeparatedSubsetSums.FourPoint119Checked
import NineSeparatedSubsetSums.FixedThird119Part0
import NineSeparatedSubsetSums.FixedThird119Part1
import NineSeparatedSubsetSums.FixedThird119Part2
import NineSeparatedSubsetSums.FixedThird119Part3
import NineSeparatedSubsetSums.FixedThird119Part4
import NineSeparatedSubsetSums.FixedThird119Part5
import NineSeparatedSubsetSums.FixedThird119Part6

namespace NineSeparatedSubsetSums

theorem fourPoint119_no_descending_tail : NoDescendingTail 119 := by
  apply noDescendingTail_of_third_tails 119 108780 max148_second119_fourPoint_moment_bound
  intro b hlo hhi
  have h0 : cachedThirdLower 119 108780 = 105 := by decide +kernel
  rw [h0] at hlo
  have upper : b < 119 := by omega
  apply noDescendingThirdTail_of_cached 119 b 108780
  · intro t ht hd
    exact max148_second119_fourPoint_moment_bound (b::t) (by simp [ht]) hd
  by_cases q0 : b < 112
  · let j : Fin 7 := ⟨b-105, by omega⟩
    have hj : 105+j.val=b := by dsimp [j]; omega
    have ok := fixedThird119Part0 j
    simpa only [hj] using ok
  by_cases q1 : b < 114
  · let j : Fin 2 := ⟨b-112, by omega⟩
    have hj : 112+j.val=b := by dsimp [j]; omega
    have ok := fixedThird119Part1 j
    simpa only [hj] using ok
  by_cases q2 : b < 115
  · let j : Fin 1 := ⟨b-114, by omega⟩
    have hj : 114+j.val=b := by dsimp [j]; omega
    have ok := fixedThird119Part2 j
    simpa only [hj] using ok
  by_cases q3 : b < 116
  · let j : Fin 1 := ⟨b-115, by omega⟩
    have hj : 115+j.val=b := by dsimp [j]; omega
    have ok := fixedThird119Part3 j
    simpa only [hj] using ok
  by_cases q4 : b < 117
  · let j : Fin 1 := ⟨b-116, by omega⟩
    have hj : 116+j.val=b := by dsimp [j]; omega
    have ok := fixedThird119Part4 j
    simpa only [hj] using ok
  by_cases q5 : b < 118
  · let j : Fin 1 := ⟨b-117, by omega⟩
    have hj : 117+j.val=b := by dsimp [j]; omega
    have ok := fixedThird119Part5 j
    simpa only [hj] using ok
  let j : Fin 1 := ⟨b-118, by omega⟩
  have hj : 118+j.val=b := by dsimp [j]; omega
  have ok := fixedThird119Part6 j
  simpa only [hj] using ok

#print axioms fourPoint119_no_descending_tail
end NineSeparatedSubsetSums
