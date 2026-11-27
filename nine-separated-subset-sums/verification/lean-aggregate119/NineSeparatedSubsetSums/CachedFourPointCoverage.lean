import NineSeparatedSubsetSums.FourPoint113Shard
import NineSeparatedSubsetSums.PairPackedCoverage112
import NineSeparatedSubsetSums.CachedFourPointShards

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- Geometry and the already checked initial range reduce the final proof
to a family of modular descending-tail exclusions. -/
theorem separated_nine_at_least_149_of_remaining_tails
    (exclude : ∀ a : ℕ, 114 ≤ a → a ≤ 147 → NoDescendingTail a)
    (w : Fin 9 → ℝ) (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ i, 149 ≤ w i := by
  apply separated_nine_at_least_149_of_integer_exclusion _ w hpos sep
  intro a ha hmax hInj
  obtain ⟨t, hlen, hd, hp, hn, ht, _⟩ :=
    integer_max148_to_search_input a (fun i => by have := (ha i).1; omega)
      (fun i => (ha i).2) hmax hInj
  have hm := max148_nat_moment_bound t hlen hn
  cases t with
  | nil => simp at hlen
  | cons b t =>
    have hb : b ≤ 147 := by
      have h := (List.pairwise_cons.mp hd).1 b (by simp)
      omega
    have inner := (List.pairwise_cons.mp hd).2
    have count : t.length = 7 := by simp at hlen; omega
    let pos : ∀ x ∈ t, 0 < x := fun x hx => hp x (by simp [hx])
    by_cases low : b ≤ 112
    · have hi : ∀ x ∈ t, x ≤ b - 1 := by
        intro x hx
        have hh := (List.pairwise_cons.mp inner).1 x hx
        omega
      have h := searchWindowedCap_true_of_completion 511 101691 t [148,b] (b-1)
        (computeSubsetMask [148,b]).1 (148+b) (148^2+b^2)
        (computeSubsetMask_correct [148,b]).1 (by simp) (by simp)
        pos hi (List.pairwise_cons.mp inner).2 hn
        (by simpa only [List.sum_cons, Nat.add_assoc] using ht)
        (by simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hm)
      rw [count] at h
      change pair_packed_second_shard b = true at h
      rw [pairPackedShardsThrough112Coverage b low] at h
      exact Bool.noConfusion h
    · by_cases h₁₁₃ : b = 113
      · subst b
        exact fourPoint113_no_descending_tail t count inner pos hn ht
      · exact exclude b (by omega) hb t count inner pos hn ht

#print axioms separated_nine_at_least_149_of_remaining_tails

end NineSeparatedSubsetSums
