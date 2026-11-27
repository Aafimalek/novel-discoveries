import NineSeparatedSubsetSums.PairPackingWindowedCap

namespace NineSeparatedSubsetSums

def pairPackedThirdLower (a : ℕ) : ℕ :=
  capacityWindow 7 (a - 1) (148 + a) (148 ^ 2 + a ^ 2) 511 101691

def pairPackedThirdCount (a : ℕ) : ℕ :=
  a - 1 + 1 - pairPackedThirdLower a

def pairPackedThirdShard (a t : ℕ) : Bool :=
  let m := (computeSubsetMask [148,a]).1
  let b := pairPackedThirdLower a + t
  if m &&& (m <<< b) = 0 then
    searchWindowedCap 511 101691 6 (b - 1) ([148,a] ++ [b])
      (addSubsetMask m b) (148+a+b) (148^2+a^2+b^2)
  else false

theorem pairPackedThirdShard_of_second_true (a : ℕ)
    (h : pair_packed_second_shard a = true) :
    ∃ t, t < pairPackedThirdCount a ∧ pairPackedThirdShard a t = true := by
  unfold pair_packed_second_shard at h
  rw [show (7 : ℕ) = 4 + 3 by rfl, searchWindowedCap] at h
  split at h
  · obtain ⟨t, ht, good⟩ := List.any_eq_true.mp h
    exact ⟨t, List.mem_range.mp ht, good⟩
  · simp at h

theorem pairPackedSecondFalse_of_third (a : ℕ)
    (h : ∀ t, t < pairPackedThirdCount a → pairPackedThirdShard a t = false) :
    pair_packed_second_shard a = false := by
  cases e : pair_packed_second_shard a with
  | false => rfl
  | true =>
    obtain ⟨t, ht, good⟩ := pairPackedThirdShard_of_second_true a e
    rw [h t ht] at good
    exact (Bool.false_ne_true good).elim

#print axioms pairPackedThirdShard_of_second_true
#print axioms pairPackedSecondFalse_of_third

end NineSeparatedSubsetSums
