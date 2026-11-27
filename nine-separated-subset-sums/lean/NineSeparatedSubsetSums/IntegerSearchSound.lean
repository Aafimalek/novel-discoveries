import NineSeparatedSubsetSums.SubsetMask
import NineSeparatedSubsetSums.SearchPruning

namespace NineSeparatedSubsetSums

/-- Candidate search with the checked bitmask representation. A false
result excludes any descending positive completion of the requested
length with the two target moments. -/
def searchIntegerWeights (minSum minSq : ℕ) :
    ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, total, square => decide (minSum ≤ total ∧ minSq ≤ square)
  | k + 1, hi, m, total, square =>
    if minSum ≤ total + topSum (k + 1) hi ∧
        minSq ≤ square + topSquare (k + 1) hi then
      (List.range hi).any (fun t =>
        let x := t + 1
        if m &&& (m <<< x) = 0 then
          searchIntegerWeights minSum minSq k (x - 1)
            (addSubsetMask m x) (total + x) (square + x ^ 2)
        else false)
    else false

private theorem prefix_sums_nodup (p q : List ℕ) (h : (natSubsetSums (p ++ q)).Nodup) :
    (natSubsetSums p).Nodup := by
  induction q using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton q a ih =>
    rw [← List.append_assoc, natSubsetSums_snoc] at h
    exact ih h.of_append_left

/-- If a valid completion exists, this executable search cannot return
false. This theorem covers each general bitmask/capacity pruning step. -/
theorem search_true_of_completion (minSum minSq : ℕ) (suffix : List ℕ)
    (hist : List ℕ) (hi m total square : ℕ)
    (hrep : maskRep (natSubsetSums hist) m)
    (hpos : ∀ i ∈ suffix, 0 < i)
    (hhi : ∀ i ∈ suffix, i ≤ hi)
    (hsort : suffix.Pairwise (· > ·))
    (hdist : (natSubsetSums (hist ++ suffix)).Nodup)
    (hsum : minSum ≤ total + suffix.sum)
    (hsq : minSq ≤ square + (suffix.map (· ^ 2)).sum) :
    searchIntegerWeights minSum minSq suffix.length hi m total square = true := by
  induction suffix generalizing hist hi m total square with
  | nil =>
    simpa [searchIntegerWeights] using (show _ ≤ total ∧ _ ≤ square from
      ⟨by simpa using hsum, by simpa using hsq⟩)
  | cons x xs ih =>
    obtain ⟨hD, hS⟩ := List.pairwise_cons.mp hsort
    have hx : 0 < x := hpos x (List.mem_cons_self)
    have hxhi : x ≤ hi := hhi x (List.mem_cons_self)
    have hpref : (natSubsetSums hist).Nodup :=
      prefix_sums_nodup hist (x :: xs) hdist
    have hfull : (natSubsetSums ((hist ++ [x]) ++ xs)).Nodup := by
      rw [List.append_assoc]
      exact hdist
    have next := prefix_sums_nodup (hist ++ [x]) xs hfull
    have mask := (addSubsetMask_collision_iff hist x m hrep hpref).mpr next
    have hcap := capacity_cut_sound (x :: xs) hi total square minSum minSq hsort hhi hsum hsq
    have hc1 : x - 1 ∈ List.range hi := List.mem_range.mpr (by omega)
    have hpx : x - 1 + 1 = x := by omega
    have hchild : searchIntegerWeights minSum minSq xs.length (x - 1)
        (addSubsetMask m x) (total + x) (square + x ^ 2) = true := by
      apply ih (hist ++ [x]) (x - 1) (addSubsetMask m x) (total + x) (square + x ^ 2)
      · exact addSubsetMask_represents hist x m hrep
      · exact fun a ha => hpos a (List.mem_cons_of_mem _ ha)
      · intro a ha
        have := hD a ha
        omega
      · exact hS
      · exact hfull
      · simpa [Nat.add_assoc] using hsum
      · simpa [Nat.add_assoc] using hsq
    change minSum ≤ total + topSum (xs.length + 1) hi ∧
      minSq ≤ square + topSquare (xs.length + 1) hi at hcap
    rw [List.length_cons, searchIntegerWeights, if_pos hcap, List.any_eq_true]
    refine ⟨x - 1, hc1, ?_⟩
    simpa [hpx, mask] using hchild

#print axioms search_true_of_completion

end NineSeparatedSubsetSums
