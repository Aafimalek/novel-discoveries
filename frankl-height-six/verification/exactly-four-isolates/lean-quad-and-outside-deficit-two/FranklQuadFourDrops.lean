import FranklLinkCliqueRegions

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

theorem ordinary_anchor_block_of_quad_and_outside {G : Finset (Finset α)} {Q : Finset α}
    {p q : α} (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 3)
    (hQ : Q ∈ quads (starBlocks G))
    (hpQ : p ∈ Q) (hq : q ∈ sources G) (hqN : q ∉ Q) :
    omittedStars G (starPairMax G p q) = {p,q} := by
  classical
  have hD := starBlocks_pairDesign hG hm
  have hQB := (Finset.mem_filter.mp hQ).1
  have hp := (hD.1 Q hQB).1 hpQ
  have hpq : p ≠ q := fun e => hqN (e ▸ hpQ)
  let A := omittedStars G (starPairMax G p q)
  have hAB : A ∈ starBlocks G := Finset.mem_image.mpr
    ⟨starPairMax G p q,starPairMax_mem hp hq hpq,rfl⟩
  obtain ⟨hpA,hqA⟩ := omittedBlock_members hp hq
  have hLo := (hD.1 A hAB).2
  have h2 : A.card = 2 := by
    by_contra hn
    have hAQ : A ≠ Q := fun e => hqN (e ▸ hqA)
    have hDis := (quad_disjoint_nonpair_and_exact_deficit hD hDeg hQ).1 A hAB
      (by omega) hAQ
    exact (Finset.disjoint_left.mp hDis) hpQ hpA
  exact omittedStars_eq_pair_of_card_two hp hq hpq h2

private theorem mate_clique_in_pair {G : Finset (Finset α)} {A U : Finset α}
    {r s : α} (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hU : U ∈ starBlocks G) (hrU : r ∈ U) (hsU : s ∉ U) (hA : A = {r,s}) :
    BlockLinkClique G A (U.erase r) := by
  apply blockLinkClique_of_incident_block hG hm hU (r := r) (by rw [hA]; simp) hrU
    (Finset.erase_subset _ _)
  rw [hA]
  apply Finset.disjoint_left.mpr
  intro x hx hxA
  obtain ⟨hxr,hxU⟩ := Finset.mem_erase.mp hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hxA
  exact hxA.elim hxr (fun e => hsU (e ▸ hxU))

/-- Two distinct blocks through one vertex have disjoint mate groups. -/
theorem mate_groups_disjoint_same_anchor {S : Finset α} {B : Finset (Finset α)}
    {U V : Finset α} {r : α}
    (hD : PairDesign S B) (hU : U ∈ B) (hV : V ∈ B) (hne : U ≠ V)
    (hrU : r ∈ U) (hrV : r ∈ V) :
    Disjoint (U.erase r) (V.erase r) := by
  have hSmall := distinct_blocks_inter_card_le_one hD hU hV hne
  apply Finset.disjoint_left.mpr
  intro x hxU hxV
  obtain ⟨hxr,hxu⟩ := Finset.mem_erase.mp hxU
  have hxv := Finset.mem_of_mem_erase hxV
  exact hxr (Finset.card_le_one_iff.mp hSmall
    (Finset.mem_inter.mpr ⟨hxu,hxv⟩) (Finset.mem_inter.mpr ⟨hrU,hrV⟩))

/-- If one anchor lies in a quad, the four-cycle obstruction cannot
occur. Its three-point mate group is disjoint from every other nonpair
group; another deficit-two anchor has one quad or two triples. -/
theorem quad_and_outside_deficitTwo_four_drops {G : Finset (Finset α)} {Q : Finset α}
    {p q : α} (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 3)
    (hQ : Q ∈ quads (starBlocks G)) (hpQ : p ∈ Q)
    (hq : q ∈ sources G) (hqN : q ∉ Q)
    (hqD : designDegree (starBlocks G) q + 3 = (sources G).card) :
    ∃ Drop, TransitivelyLinkedDeletion G (omittedStars G (starPairMax G p q)) Drop ∧
      Drop.card = 4 := by
  classical
  let B := starBlocks G
  let A := omittedStars G (starPairMax G p q)
  let E := Q.erase p
  have hD := starBlocks_pairDesign hG hm
  have h4 := (deficit_le_two_local_classification hD hDeg).1
  have hQb := (Finset.mem_filter.mp hQ).1
  have hQc := (Finset.mem_filter.mp hQ).2
  have hA : A = {p,q} := ordinary_anchor_block_of_quad_and_outside hG hm hDeg hQ hpQ hq hqN
  have hA' : A = {q,p} := hA.trans (Finset.pair_comm p q)
  have hE : BlockLinkClique G A E := mate_clique_in_pair hG hm hQb hpQ hqN hA
  have hEc : E.card = 3 := by
    have hc : E.card + 1 = Q.card := Finset.card_erase_add_one hpQ
    omega
  have hEN : E.Nonempty := Finset.card_pos.mp (by omega)
  have hNoQ := (quad_disjoint_nonpair_and_exact_deficit hD hDeg hQ).1
  have hQD := designDegree_add_triple_quad hD h4 hq
  have hAux {U : Finset α} (hU : U ∈ B) (hqU : q ∈ U) (hUc : 3 ≤ U.card) :
      BlockLinkClique G A (U.erase q) ∧ Disjoint E (U.erase q) := by
    have hUQ : U ≠ Q := fun e => hqN (e ▸ hqU)
    have hDis := hNoQ U hU hUc hUQ
    have hpU : p ∉ U := (Finset.disjoint_left.mp hDis) hpQ
    refine ⟨mate_clique_in_pair hG hm hU hqU hpU hA',?_⟩
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.disjoint_left.mp hDis) (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy)
  by_cases hQpos : 0 < quadDegree B q
  · obtain ⟨U,hU'⟩ := Finset.card_pos.mp hQpos
    obtain ⟨hUquad,hqU⟩ := Finset.mem_filter.mp hU'
    obtain ⟨hU,hUc⟩ := Finset.mem_filter.mp hUquad
    obtain ⟨hF,hDis⟩ := hAux hU hqU (by omega)
    have hc := Finset.card_erase_add_one hqU
    have hFN : (U.erase q).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨Drop,hDrop,hcD⟩ := transitiveDeletion_of_two_link_cliques hE hF hEN hFN hDis
    exact ⟨Drop,hDrop,by omega⟩
  · have hTwo : 2 ≤ tripleDegree B q := by
      change ¬ 0 < quadDegree (starBlocks G) q at hQpos
      change 2 ≤ tripleDegree (starBlocks G) q
      omega
    obtain ⟨U,hU',V,hV',hne⟩ := Finset.one_lt_card.mp (show 1 < tripleDegree B q by omega)
    obtain ⟨hUt,hqU⟩ := Finset.mem_filter.mp hU'
    obtain ⟨hVt,hqV⟩ := Finset.mem_filter.mp hV'
    obtain ⟨hU,hUc⟩ := Finset.mem_filter.mp hUt
    obtain ⟨hV,hVc⟩ := Finset.mem_filter.mp hVt
    obtain ⟨hF,hEF⟩ := hAux hU hqU (by omega)
    obtain ⟨hH,hEH⟩ := hAux hV hqV (by omega)
    have hFH := mate_groups_disjoint_same_anchor hD hU hV hne hqU hqV
    have hcF := Finset.card_erase_add_one hqU
    have hcH := Finset.card_erase_add_one hqV
    have hFN : (U.erase q).Nonempty := Finset.card_pos.mp (by omega)
    have hHN : (V.erase q).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨Drop,hDrop,hcD⟩ :=
      transitiveDeletion_of_three_link_cliques hE hF hH hEN hFN hHN hEF hEH hFH
    exact ⟨Drop,hDrop,by omega⟩

theorem quad_and_outside_deficitTwo_impossible {G : Finset (Finset α)} {Q : Finset α}
    {p q : α} (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 3)
    (hQ : Q ∈ quads (starBlocks G)) (hpQ : p ∈ Q)
    (hq : q ∈ sources G) (hqN : q ∉ Q)
    (hqD : designDegree (starBlocks G) q + 3 = (sources G).card) : False := by
  have hD := starBlocks_pairDesign hG hm
  have hp := (hD.1 Q (Finset.mem_filter.mp hQ).1).1 hpQ
  have hpq : p ≠ q := fun e => hqN (e ▸ hpQ)
  have hpD := (quad_disjoint_nonpair_and_exact_deficit hD hDeg hQ).2 p hpQ
  have hA := ordinary_anchor_block_of_quad_and_outside hG hm hDeg hQ hpQ hq hqN
  obtain ⟨Drop,hDrop,hDropC⟩ := quad_and_outside_deficitTwo_four_drops hG hm hDeg hQ hpQ hq hqN hqD
  exact exact_four_deficit_two_ordinary_pair_not_four_linked_drops hG hm hI hDeg hp hq hpq
    hpD hqD hA hDrop (by omega)

#print axioms ordinary_anchor_block_of_quad_and_outside
#print axioms mate_groups_disjoint_same_anchor
#print axioms quad_and_outside_deficitTwo_four_drops
#print axioms quad_and_outside_deficitTwo_impossible
end FranklForcingFiber
