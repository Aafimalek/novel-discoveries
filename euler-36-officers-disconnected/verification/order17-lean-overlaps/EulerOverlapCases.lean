import EulerOverlapClauses

namespace LatinGap.PairEncoding
open Finset
open scoped BigOperators

theorem two_overlaps_four_candidates {D : Design 6} (hD : Linear D)
    {p : PairKey 6} (low : UnusedLow D p) {k : Coord} (hi : p.i ≠ k) (hj : p.j ≠ k)
    {a b : Fin 6} (dist : a ≠ b) (ha : Overlap D p k a) (hb : Overlap D p k b) :
    4 ≤ (candidates D (p.i,p.a) (p.j,p.b) k).card := by
  let N := neighbors D (p.i,p.a) k
  let M := neighbors D (p.j,p.b) k
  have hN : N.card = 2 := (card_neighbors hD hi).trans low.2.1
  have hM : M.card = 2 := (card_neighbors hD hj).trans low.2.2
  have hI : ({a,b} : Finset (Fin 6)) ⊆ N ∩ M := by
    intro u hu
    simp only [mem_insert,mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact mem_inter.mpr ⟨(mem_neighbors hi).2 ha.1,(mem_neighbors hj).2 ha.2⟩
    · exact mem_inter.mpr ⟨(mem_neighbors hi).2 hb.1,(mem_neighbors hj).2 hb.2⟩
  have hc := card_le_card hI
  have hpair : ({a,b} : Finset (Fin 6)).card = 2 := by simp [dist]
  rw [hpair] at hc
  have hu := card_union_add_card_inter N M
  have hu2 : (N ∪ M).card ≤ 2 := by omega
  change 4 ≤ (univ \ (N ∪ M)).card
  rw [card_sdiff_of_subset (subset_univ _)]
  simp only [card_univ, Fintype.card_fin]
  omega

/-- Two shared neighbors on one side and another on the other would force
a saturated 4-by-3 rectangle and frequency budget at least 18. -/
theorem two_overlaps_forbid_opposite {D : Design 6} (hD : Linear D) (hS : Saturated D)
    (size : D.card = 17) (hm : ∀ x : Label 6, 2 ≤ freq D x) {p : PairKey 6}
    (low : UnusedLow D p) {k l : Coord} (hik : p.i ≠ k) (hjk : p.j ≠ k)
    (hil : p.i ≠ l) (hjl : p.j ≠ l) (hkl : k ≠ l)
    {a b c : Fin 6} (dist : a ≠ b) (ha : Overlap D p k a) (hb : Overlap D p k b) :
    ¬ Overlap D p l c := by
  intro hc
  have hK := two_overlaps_four_candidates hD low hik hjk dist ha hb
  have hL := card_candidates_shared hD hil hjl hc.1 hc.2
  have hL3 : 3 ≤ (candidates D (p.i,p.a) (p.j,p.b) l).card := by
    rw [low.2.1, low.2.2] at hL
    omega
  -- Use the opposite side: three vertices of degree at least four.
  obtain ⟨C,hC,hC3⟩ := exists_subset_card_eq hL3
  let E := univ \ C
  have hE3 : E.card = 3 := by simp [E,card_sdiff_of_subset (subset_univ C),hC3]
  have hCdeg (x : Fin 6) (hx : x ∈ C) : 4 ≤ freq D (l,x) := by
    apply hK.trans
    exact card_candidates_le_freq hD hkl.symm (fun y hy =>
      candidate_rectangle hS (ne_of_lt p.increasing) hil hik hjl hjk hkl.symm low.1 (hC hx) hy)
  have hC12 : 12 ≤ ∑ x ∈ C, freq D (l,x) := by
    simpa [hC3] using (sum_le_sum (fun x hx => hCdeg x hx) :
      (∑ x ∈ C, 4) ≤ ∑ x ∈ C, freq D (l,x))
  have hE6 : 6 ≤ ∑ x ∈ E, freq D (l,x) := by
    simpa [hE3] using (sum_le_sum (fun x _ => hm (l,x)) :
      (∑ x ∈ E, 2) ≤ ∑ x ∈ E, freq D (l,x))
  have total := sum_sdiff (f := fun x : Fin 6 => freq D (l,x)) (subset_univ C)
  change (∑ x ∈ E, freq D (l,x)) + (∑ x ∈ C, freq D (l,x)) = ∑ x : Fin 6, freq D (l,x) at total
  rw [sum_freq, size] at total
  omega

#print axioms two_overlaps_four_candidates
#print axioms two_overlaps_forbid_opposite
end LatinGap.PairEncoding
