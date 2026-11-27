import NineSeparatedSubsetSums.IntegerSearchInput

namespace NineSeparatedSubsetSums

/-- Fix second-largest weight a, so each certificate can be checked
separately. The seven remaining weights are below a. -/
def integer_second_shard (a : ℕ) : Bool :=
  searchIntegerWeights 511 87381 7 (a - 1) (computeSubsetMask [148, a]).1
    (148 + a) (148 ^ 2 + a ^ 2)

/-- A concrete exact specification for sharded max-148 exclusion. -/
theorem integer_counterexample_hits_shard (w : Fin 9 → ℤ)
    (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148)
    (distinct : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i)) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 147 ∧ integer_second_shard a = true := by
  obtain ⟨t, hlen, hd, hp, hn, ht, hm⟩ :=
    integer_max148_to_search_input w positive bounded last distinct
  cases t with
  | nil => simp at hlen
  | cons a t =>
    have ha : 1 ≤ a := hp a (by simp)
    have b : a ≤ 147 := by
      have h := (List.pairwise_cons.mp hd).1 a (by simp)
      omega
    have inner := (List.pairwise_cons.mp hd).2
    have hsmall : ∀ x ∈ t, x ≤ a - 1 := by
      intro x h
      have hh := (List.pairwise_cons.mp inner).1 x h
      omega
    have count : t.length = 7 := by simp at hlen; omega
    have rp : maskRep (natSubsetSums [148, a]) (computeSubsetMask [148,a]).1 :=
      (computeSubsetMask_correct [148,a]).1
    have h := search_true_of_completion 511 87381 t [148,a] (a - 1)
      (computeSubsetMask [148,a]).1 (148 + a) (148 ^ 2 + a ^ 2) rp
      (fun x hx => hp x (by simp [hx])) hsmall (List.pairwise_cons.mp inner).2 hn
      (by simpa only [List.sum_cons, Nat.add_assoc] using ht)
      (by simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hm)
    rw [count] at h
    exact ⟨a, ha, b, h⟩

/-- Certification only needs the finite shard Boolean facts, not another
unproved domain reduction. -/
theorem integer_max148_excluded_of_shards
    (checks : ∀ a : ℕ, 1 ≤ a → a ≤ 147 → integer_second_shard a = false)
    (w : Fin 9 → ℤ) (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148) :
    ¬ Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i) := by
  intro h
  obtain ⟨a, ha, hb, hc⟩ := integer_counterexample_hits_shard w positive bounded last h
  rw [checks a ha hb] at hc
  exact Bool.false_ne_true hc

example : integer_second_shard 1 = false := by decide

#print axioms integer_counterexample_hits_shard
#print axioms integer_max148_excluded_of_shards

end NineSeparatedSubsetSums
