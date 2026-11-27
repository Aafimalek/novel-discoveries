import NineSeparatedSubsetSums.FourPoint113Shard
import NineSeparatedSubsetSums.PairPackedCoverage112

open scoped BigOperators

namespace NineSeparatedSubsetSums

theorem counterexample_hits_pair_packed_shard_above_113 (w : Fin 9 → ℤ)
    (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148)
    (distinct : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i)) :
    ∃ a : ℕ, 114 ≤ a ∧ a ≤ 147 ∧ pair_packed_second_shard a = true := by
  obtain ⟨t, hlen, hd, hp, hn, ht, _⟩ :=
    integer_max148_to_search_input w positive bounded last distinct
  have hm := max148_nat_moment_bound t hlen hn
  cases t with
  | nil => simp at hlen
  | cons a t =>
    have hb : a ≤ 147 := by
      have h := (List.pairwise_cons.mp hd).1 a (by simp)
      omega
    have inner := (List.pairwise_cons.mp hd).2
    have hsmall : ∀ x ∈ t, x ≤ a - 1 := by
      intro x hx
      have hh := (List.pairwise_cons.mp inner).1 x hx
      omega
    have count : t.length = 7 := by simp at hlen; omega
    let pos : ∀ x ∈ t, 0 < x := fun x hx => hp x (by simp [hx])
    have h := searchWindowedCap_true_of_completion 511 101691 t [148,a] (a - 1)
      (computeSubsetMask [148,a]).1 (148+a) (148^2+a^2)
      (computeSubsetMask_correct [148,a]).1 (by simp) (by simp)
      pos hsmall (List.pairwise_cons.mp inner).2 hn
      (by simpa only [List.sum_cons, Nat.add_assoc] using ht)
      (by simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hm)
    rw [count] at h
    change pair_packed_second_shard a = true at h
    have hlo : ¬ a ≤ 112 := by
      intro aLo
      rw [pairPackedShardsThrough112Coverage a aLo] at h
      exact Bool.false_ne_true h
    have nEq : a ≠ 113 := by
      intro eq
      subst a
      exact fourPoint113_no_descending_tail t count inner pos hn ht
    exact ⟨a,by omega,hb,h⟩

/-- Updated full-theorem obligation: the checked special 113 branch was
closed using the stronger four-point threshold. -/
theorem separated_nine_at_least_149_of_remaining_shards_above_113
    (checks : ∀ a : ℕ, 114 ≤ a → a ≤ 147 → pair_packed_second_shard a = false)
    (w : Fin 9 → ℝ) (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ i, 149 ≤ w i := by
  apply separated_nine_at_least_149_of_integer_exclusion _ w hpos sep
  intro a ha hmax hInj
  obtain ⟨q,hlo,hhi,hq⟩ := counterexample_hits_pair_packed_shard_above_113 a
    (fun i => by have := (ha i).1; omega) (fun i => (ha i).2) hmax hInj
  rw [checks q hlo hhi] at hq
  exact Bool.false_ne_true hq

#print axioms counterexample_hits_pair_packed_shard_above_113
#print axioms separated_nine_at_least_149_of_remaining_shards_above_113

end NineSeparatedSubsetSums
