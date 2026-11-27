import NineSeparatedSubsetSums.PairPackingWeights
import NineSeparatedSubsetSums.IntegerSearchWindowedCap

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- The existing checked terminal-window search with the pair-packing
square threshold. -/
def pair_packed_second_shard (a : ℕ) : Bool :=
  searchWindowedCap 511 101691 7 (a - 1) [148,a] (computeSubsetMask [148,a]).1
    (148 + a) (148 ^ 2 + a ^ 2)

theorem counterexample_hits_pair_packed_shard (w : Fin 9 → ℤ)
    (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148)
    (distinct : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i)) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 147 ∧ pair_packed_second_shard a = true := by
  obtain ⟨t, hlen, hd, hp, hn, ht, _⟩ :=
    integer_max148_to_search_input w positive bounded last distinct
  have hm := max148_nat_moment_bound t hlen hn
  cases t with
  | nil => simp at hlen
  | cons a t =>
    have ha : 1 ≤ a := hp a (by simp)
    have hb : a ≤ 147 := by
      have h := (List.pairwise_cons.mp hd).1 a (by simp)
      omega
    have inner := (List.pairwise_cons.mp hd).2
    have hsmall : ∀ x ∈ t, x ≤ a - 1 := by
      intro x h
      have hh := (List.pairwise_cons.mp inner).1 x h
      omega
    have count : t.length = 7 := by simp at hlen; omega
    have h := searchWindowedCap_true_of_completion 511 101691 t [148,a] (a - 1)
      (computeSubsetMask [148,a]).1 (148+a) (148^2+a^2)
      (computeSubsetMask_correct [148,a]).1 (by simp) (by simp)
      (fun x hx => hp x (by simp [hx])) hsmall (List.pairwise_cons.mp inner).2 hn
      (by simpa only [List.sum_cons, Nat.add_assoc] using ht)
      (by simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hm)
    rw [count] at h
    exact ⟨a, ha, hb, h⟩

theorem integer_max148_excluded_of_pair_packed_shards
    (checks : ∀ a : ℕ, 1 ≤ a → a ≤ 147 → pair_packed_second_shard a = false)
    (w : Fin 9 → ℤ) (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148) :
    ¬ Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i) := by
  intro h
  obtain ⟨a,ha,hb,hs⟩ := counterexample_hits_pair_packed_shard w positive bounded last h
  rw [checks a ha hb] at hs
  exact Bool.false_ne_true hs

#print axioms counterexample_hits_pair_packed_shard
#print axioms integer_max148_excluded_of_pair_packed_shards

end NineSeparatedSubsetSums
