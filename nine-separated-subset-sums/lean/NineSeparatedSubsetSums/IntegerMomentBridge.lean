import NineSeparatedSubsetSums.SignedMoment
import NineSeparatedSubsetSums.PackingMoment
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- The ordinary and signed sums use the same list of subset choices.
Each ordinary subset sum is doubled, then centered by the total weight. -/
theorem signedSums_eq_centered_sublists (xs : List ℤ) :
    signedSums xs = xs.sublists.map (fun s => 2 * s.sum - xs.sum) := by
  induction xs with
  | nil => simp [signedSums]
  | cons a xs ih =>
    rw [show signedSums (a :: xs) = spread a (signedSums xs) from rfl, ih]
    simp only [spread, List.flatMap_map, List.sublists_cons, List.bind_eq_flatMap,
      List.map_flatMap]
    congr 1
    funext s
    simp only [List.sum_cons, List.map_cons, List.map_nil]
    congr 1 <;> ring_nf

/-- Rank gaps for an increasing integer sequence follow from its unit increment bound. -/
theorem unitGap_of_adjacent (g : ℕ → ℤ) (n : ℕ)
    (adjacent : ∀ j, j + 1 < n → g j + 1 ≤ g (j + 1)) :
    ∀ i j, i ≤ j → j < n → ((j : ℤ) - (i : ℤ)) ≤ g j - g i := by
  intro i j
  induction j generalizing i with
  | zero =>
    intro h _
    have hi : i = 0 := Nat.eq_zero_of_le_zero h
    subst i
    simp
  | succ j ih =>
    intro hij hj
    by_cases h : i ≤ j
    · have hp := ih i h (by omega)
      have hn := adjacent j hj
      omega
    · have he : i = j.succ := by omega
      subst i
      simp

private theorem sum_range_list_getD (ys : List ℤ) (F : ℤ → ℤ) :
    (∑ i ∈ Finset.range ys.length, F (ys[i]?.getD 0)) = (ys.map F).sum := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      ih, List.map_cons, List.sum_cons, add_comm]

/-- Nine integer weights with distinct subset sums have squared-weight
sum at least 87381. Every position in the input list is a distinct
subset choice, including when the values in those positions happen
to coincide. No positivity or maximum assumption is required. -/
theorem integerMomentBoundOfDistinctSublists (xs : List ℤ) (len : xs.length = 9)
    (distinct : (xs.sublists.map List.sum).Nodup) :
    87381 ≤ (xs.map (· ^ 2)).sum := by
  let ss : List ℤ := xs.sublists.map List.sum
  let ranked : List ℤ := ss.mergeSort (fun a b => decide (a ≤ b))
  have perm : ranked.Perm ss := List.mergeSort_perm _ _
  have rankedNodup : ranked.Nodup := perm.nodup_iff.mpr distinct
  have sorted : ranked.Pairwise (· ≤ ·) := by
    exact List.pairwise_mergeSort' (· ≤ ·) ss
  have n : ranked.length = 512 := by
    rw [perm.length_eq]
    simp [ss, List.length_sublists, len]
  let g (i : ℕ) : ℤ := ranked[i]?.getD 0
  have getG (i : ℕ) (hi : i < ranked.length) : g i = ranked[i] := by
    simp [g, List.getElem?_eq_getElem hi]
  have adj : ∀ j, j + 1 < 512 → g j + 1 ≤ g (j + 1) := by
    intro j hj
    have ha : j < ranked.length := by omega
    have hb : j + 1 < ranked.length := by omega
    have hs := sorted.rel_getElem_of_lt ha hb (by omega)
    have hd := (List.nodup_iff_pairwise_ne.mp rankedNodup).rel_getElem_of_lt ha hb (by omega)
    rw [getG j ha, getG (j+1) hb]
    omega
  let f (i : ℕ) : ℤ := 2 * g i - xs.sum
  have spacing : ∀ i j : ℕ, i ≤ j → j < 512 →
      2 * ((j : ℤ) - (i : ℤ)) ≤ f j - f i := by
    intro i j hij hj
    have hp := unitGap_of_adjacent g 512 adj i j hij hj
    dsimp [f]
    omega
  have pack := momentOfRankedSignedScores f spacing
  let scoreSquare (s : ℤ) : ℤ := (2*s - xs.sum)^2
  have he : (∑ i ∈ Finset.range 512, (f i)^2) = (ranked.map scoreSquare).sum := by
    change (∑ i ∈ Finset.range 512, scoreSquare (ranked[i]?.getD 0)) =
      (ranked.map scoreSquare).sum
    rw [← n, sum_range_list_getD]
  have hRankedScores : (ranked.map scoreSquare).sum = ((signedSums xs).map (· ^ 2)).sum := by
    rw [(perm.map scoreSquare).sum_eq, signedSums_eq_centered_sublists]
    simp [ss, scoreSquare, List.map_map, Function.comp_def]
  rw [he, hRankedScores, signedSums_sum_sq, len] at pack
  norm_num at pack
  omega

#print axioms signedSums_eq_centered_sublists
#print axioms unitGap_of_adjacent
#print axioms integerMomentBoundOfDistinctSublists

end NineSeparatedSubsetSums
