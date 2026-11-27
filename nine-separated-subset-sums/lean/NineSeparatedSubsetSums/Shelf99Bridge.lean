import NineSeparatedSubsetSums.IntegerMomentBridge
import NineSeparatedSubsetSums.Shelf99Arithmetic
import Mathlib.Data.List.Nodup

namespace NineSeparatedSubsetSums

private theorem interval_of_seventy_integer_scores (ss : List ℤ) (len : ss.length = 70)
    (distinct : ss.Nodup) (lo hi : ℤ) (bounds : ∀ z ∈ ss, lo ≤ z ∧ z ≤ hi) :
    69 ≤ hi - lo := by
  let ranked : List ℤ := ss.mergeSort (fun a b => decide (a ≤ b))
  have perm : ranked.Perm ss := List.mergeSort_perm _ _
  have rankedNodup : ranked.Nodup := perm.nodup_iff.mpr distinct
  have sorted : ranked.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) ss
  have n : ranked.length = 70 := perm.length_eq.trans len
  let g (i : ℕ) : ℤ := ranked[i]?.getD 0
  have getG (i : ℕ) (hi : i < ranked.length) : g i = ranked[i] := by
    simp [g, List.getElem?_eq_getElem hi]
  have adj : ∀ j, j + 1 < 70 → g j + 1 ≤ g (j + 1) := by
    intro j hj
    have ha : j < ranked.length := by omega
    have hb : j + 1 < ranked.length := by omega
    have hs := sorted.rel_getElem_of_lt ha hb (by omega)
    have hd := (List.nodup_iff_pairwise_ne.mp rankedNodup).rel_getElem_of_lt ha hb (by omega)
    rw [getG j ha, getG (j+1) hb]
    omega
  have hlo : lo ≤ g 0 := by
    have h0 : 0 < ranked.length := by omega
    rw [getG 0 h0]
    exact (bounds _ (perm.mem_iff.mp (List.mem_of_getElem rfl))).1
  have hhi : g 69 ≤ hi := by
    have h69 : 69 < ranked.length := by omega
    rw [getG 69 h69]
    exact (bounds _ (perm.mem_iff.mp (List.mem_of_getElem rfl))).2
  have hg := unitGap_of_adjacent g 70 adj 0 69 (by decide) (by decide)
  omega

private theorem fourSumsBounds (a b c d e f g h : ℤ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hef : e < f) (hfg : f < g) (hgh : g < h) :
    ∀ s ∈ ([a,b,c,d,e,f,g,h].sublistsLen 4),
      a+b+c+d ≤ s.sum ∧ s.sum ≤ e+f+g+h := by
  intro s hs
  change s ∈ [
    [e,f,g,h], [d,f,g,h], [d,e,g,h], [d,e,f,h], [d,e,f,g],
    [c,f,g,h], [c,e,g,h], [c,e,f,h], [c,e,f,g], [c,d,g,h],
    [c,d,f,h], [c,d,f,g], [c,d,e,h], [c,d,e,g], [c,d,e,f],
    [b,f,g,h], [b,e,g,h], [b,e,f,h], [b,e,f,g], [b,d,g,h],
    [b,d,f,h], [b,d,f,g], [b,d,e,h], [b,d,e,g], [b,d,e,f],
    [b,c,g,h], [b,c,f,h], [b,c,f,g], [b,c,e,h], [b,c,e,g],
    [b,c,e,f], [b,c,d,h], [b,c,d,g], [b,c,d,f], [b,c,d,e],
    [a,f,g,h], [a,e,g,h], [a,e,f,h], [a,e,f,g], [a,d,g,h],
    [a,d,f,h], [a,d,f,g], [a,d,e,h], [a,d,e,g], [a,d,e,f],
    [a,c,g,h], [a,c,f,h], [a,c,f,g], [a,c,e,h], [a,c,e,g],
    [a,c,e,f], [a,c,d,h], [a,c,d,g], [a,c,d,f], [a,c,d,e],
    [a,b,g,h], [a,b,f,h], [a,b,f,g], [a,b,e,h], [a,b,e,g],
    [a,b,e,f], [a,b,d,h], [a,b,d,g], [a,b,d,f], [a,b,d,e],
    [a,b,c,h], [a,b,c,g], [a,b,c,f], [a,b,c,e], [a,b,c,d]
  ] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with 
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [List.sum_cons, List.sum_nil, add_zero]
    constructor <;> omega

/-- All sorted nine-weight integer sets with maximum 148 and second
weight at most 99 fail distinctness of subset sums. -/
theorem noDistinctSublistsMax148SecondLe99
    (a b c d e f g h : ℤ)
    (apos : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e) (hef : e < f) (hfg : f < g) (hgh : g < h) (hhi : h ≤ 99) :
    ¬ ([a,b,c,d,e,f,g,h,148].sublists.map List.sum).Nodup := by
  intro distinct
  have moment0 := integerMomentBoundOfDistinctSublists [a,b,c,d,e,f,g,h,148] rfl distinct
  have moment : 87381 ≤ a^2+b^2+c^2+d^2+e^2+f^2+g^2+h^2+148^2 := by
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
      using moment0
  have m₁ : [e,h] ∈ [a,b,c,d,e,f,g,h,148].sublists := by
    apply List.mem_sublists.mpr
    exact List.Sublist.cons a (List.Sublist.cons b (List.Sublist.cons c (List.Sublist.cons d
      (List.Sublist.cons_cons e (List.Sublist.cons f (List.Sublist.cons g
        (List.Sublist.cons_cons h (List.nil_sublist _))))))))
  have m₂ : [f,g] ∈ [a,b,c,d,e,f,g,h,148].sublists := by
    apply List.mem_sublists.mpr
    exact List.Sublist.cons a (List.Sublist.cons b (List.Sublist.cons c (List.Sublist.cons d
      (List.Sublist.cons e (List.Sublist.cons_cons f (List.Sublist.cons_cons g
        (List.nil_sublist _)))))))
  have noPair : e+h ≠ f+g := by
    intro same
    have eq : [e,h] = [f,g] := by
      apply List.inj_on_of_nodup_map distinct m₁ m₂
      simpa only [List.sum_cons, List.sum_nil, add_zero] using same
    have heq : e = f := by simpa using congrArg List.head? eq
    omega
  have smallNodup : ([a,b,c,d,e,f,g,h] : List ℤ).Nodup := by
    exact (List.Nodup.of_map List.sum distinct).of_sublists.sublist
      (List.sublist_append_left [a,b,c,d,e,f,g,h] [148])
  let small : List ℤ := [a,b,c,d,e,f,g,h]
  let comb := small.sublistsLen 4
  let vals := comb.map List.sum
  have len : vals.length = 70 := by
    simp [vals, comb, small]
  have lift {s : List ℤ} (hm : s ∈ comb) : s ∈ [a,b,c,d,e,f,g,h,148].sublists := by
    apply List.mem_sublists.mpr
    exact ((List.mem_sublistsLen.mp hm).1).trans (List.sublist_append_left small [148])
  have vd : vals.Nodup := by
    apply (List.nodup_sublistsLen 4 smallNodup).map_on
    intro x hx y hy eq
    exact List.inj_on_of_nodup_map distinct (lift hx) (lift hy) eq
  have lohi : ∀ z ∈ vals, a+b+c+d ≤ z ∧ z ≤ e+f+g+h := by
    intro z hz
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
    exact fourSumsBounds a b c d e f g h hab hbc hcd hde hef hfg hgh s hs
  have span := interval_of_seventy_integer_scores vals len vd (a+b+c+d) (e+f+g+h) lohi
  have cap := secondLe99MomentUpper a b c d e f g h apos hab hbc hcd hde hef hfg hgh hhi noPair span
  omega

#print axioms noDistinctSublistsMax148SecondLe99

end NineSeparatedSubsetSums
