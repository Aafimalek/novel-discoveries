import NineSeparatedSubsetSums.IntegerSearchWindowedCap

namespace NineSeparatedSubsetSums

/-- Number of eligible first choices after fixing the two largest weights. -/
def terminalThirdCount (a : ℕ) : ℕ :=
  a - 1 + 1 - capacityWindow 7 (a - 1) (148 + a) (148 ^ 2 + a ^ 2) 511 87381

/-- Subcase at offset t from the first eligible third-largest weight. -/
def terminalThirdShard (a t : ℕ) : Bool :=
  let m := (computeSubsetMask [148,a]).1
  let b := capacityWindow 7 (a - 1) (148 + a) (148 ^ 2 + a ^ 2) 511 87381 + t
  if m &&& (m <<< b) = 0 then
    searchWindowedCap 511 87381 6 (b - 1) ([148,a] ++ [b])
      (addSubsetMask m b) (148+a+b) (148^2+a^2+b^2)
  else false

/-- Every true whole shard induces a true bounded subcase, enabling small
kernel evaluations of disjoint subcases instead of one oversized evaluation. -/
theorem terminalThirdShard_of_second_true (a : ℕ)
    (h : windowed_cap_second_shard a = true) :
    ∃ t, t < terminalThirdCount a ∧ terminalThirdShard a t = true := by
  unfold windowed_cap_second_shard at h
  rw [show (7 : ℕ) = 4 + 3 by rfl, searchWindowedCap] at h
  split at h
  · obtain ⟨t, ht, hgood⟩ := List.any_eq_true.mp h
    exact ⟨t, List.mem_range.mp ht, hgood⟩
  · simp at h

/-- Verification of bounded third subcases is sufficient to close a second
shard with no appeal to compiled evaluation. -/
theorem terminalSecondFalse_of_third (a : ℕ)
    (h : ∀ t, t < terminalThirdCount a → terminalThirdShard a t = false) :
    windowed_cap_second_shard a = false := by
  cases e : windowed_cap_second_shard a with
  | false => rfl
  | true =>
    obtain ⟨t, ht, good⟩ := terminalThirdShard_of_second_true a e
    rw [h t ht] at good
    exact (Bool.false_ne_true good).elim

#print axioms terminalThirdShard_of_second_true
#print axioms terminalSecondFalse_of_third

end NineSeparatedSubsetSums
