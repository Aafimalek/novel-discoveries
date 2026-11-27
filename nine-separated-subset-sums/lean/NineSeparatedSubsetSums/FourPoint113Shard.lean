import NineSeparatedSubsetSums.FourPoint113Checked
import NineSeparatedSubsetSums.PairPackingWindowedCap

namespace NineSeparatedSubsetSums

def fourPointWindow113 : Bool :=
  searchWindowedCap 511 109140 7 112 [148,113] (computeSubsetMask [148,113]).1
    (148+113) (148^2+113^2)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPointWindow113_false : fourPointWindow113 = false := by decide +kernel

/-- The new four-point bound and a kernel check exclude the actual
second-largest-113 branch, not just a loose set of weak-bound candidates. -/
theorem fourPoint113_no_descending_tail (tail : List ℕ)
    (len : tail.length=7)
    (desc : (113::tail).Pairwise (· > ·))
    (pos : ∀ x ∈ tail, 0 < x)
    (distinct : (natSubsetSums (148::113::tail)).Nodup)
    (total : 511 ≤ (148::113::tail).sum) : False := by
  have hm := max148_second113_fourPoint_moment_bound tail len distinct
  have hi : ∀ x ∈ tail, x ≤ 112 := by
    intro x hx
    have h := (List.pairwise_cons.mp desc).1 x hx
    omega
  have h := searchWindowedCap_true_of_completion 511 109140 tail [148,113] 112
    (computeSubsetMask [148,113]).1 (148+113) (148^2+113^2)
    (computeSubsetMask_correct [148,113]).1 (by simp) (by simp)
    pos hi (List.pairwise_cons.mp desc).2 distinct
    (by simpa only [List.sum_cons, Nat.add_assoc] using total)
    (by simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hm)
  rw [len] at h
  change fourPointWindow113 = true at h
  rw [fourPointWindow113_false] at h
  exact Bool.false_ne_true h

#print axioms fourPointWindow113_false
#print axioms fourPoint113_no_descending_tail

end NineSeparatedSubsetSums
