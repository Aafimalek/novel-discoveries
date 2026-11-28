import FranklPairDesignDeficitTwo
import FranklDeficitAtMostOneEndpoint
import FranklTripleLinks

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

theorem exact_four_deficit_le_two_not_sole_quad {G : Finset (Finset α)} {T : Finset α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 3)
    (hQ : quads (starBlocks G) = {T}) (hT : triples (starBlocks G) = ∅) : False := by
  classical
  let k := (sources G).card
  have hD := starBlocks_pairDesign hG hm
  have hQm : T ∈ quads (starBlocks G) := by rw [hQ]; simp
  obtain ⟨hTB,hTc⟩ := Finset.mem_filter.mp hQm
  have hTS := (hD.1 T hTB).1
  obtain ⟨p,hpT,q,hqT,hpq⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  have hp := hTS hpT
  have hq := hTS hqT
  have hE := (quad_disjoint_nonpair_and_exact_deficit hD hDeg hQm).2
  have hA := omitted_block_eq_of_contains_anchor_pair hG hm hp hq hpq hTB hpT hqT
  have hlo := pair_lower_with_explicit_deficits (dp := 2) (dq := 2) hG hm hI hp hq hpq
    (hE p hpT) (hE q hqT) (∅ : Finset (α × Finset α)) (by simp)
  simp only [Finset.card_empty,Nat.add_zero] at hlo
  have hup := cross_pair_actual_upper_of_omitted hG hm hp hq hpq
  dsimp only at hup
  rw [hA,hTc,hI] at hup
  have hk : 4 ≤ k := by
    have hc : T.card ≤ k := Finset.card_le_card hTS
    omega
  have hnom : 4 + ((sources G).card - 4) = k := by change 4 + (k - 4) = k; omega
  rw [hnom] at hup
  have hBudget := (deficit_le_two_global_budgets hD hDeg).1
  rw [hQ,hT,Finset.card_empty,Finset.card_singleton] at hBudget
  change (starBlocks G).card + 2 * 0 + 5 * 1 = k.choose 2 at hBudget
  change (starBlocks G).card + k + 6 + 2 + 2 ≤ _ at hlo
  omega

/-- For at most four sources, two triple blocks cannot occur at all:
their compulsory two-point overlap contradicts pair uniqueness. -/
theorem triples_card_le_one_of_support_le_four {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B) (h4 : S.card ≤ 4) : (triples B).card ≤ 1 := by
  classical
  by_contra hn
  obtain ⟨A,hA,C,hC,hne⟩ := Finset.one_lt_card.mp
    (show 1 < (triples B).card by omega)
  obtain ⟨hAB,hAc⟩ := Finset.mem_filter.mp hA
  obtain ⟨hCB,hCc⟩ := Finset.mem_filter.mp hC
  have hSmall := distinct_blocks_inter_card_le_one hD hAB hCB hne
  have hU := Finset.card_le_card
    (Finset.union_subset (hD.1 A hAB).1 (hD.1 C hCB).1)
  have hCount := Finset.card_union_add_card_inter A C
  omega

theorem exact_four_deficit_le_two_not_small_sources {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4) (hk : 2 ≤ (sources G).card) (hsmall : (sources G).card ≤ 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 3) :
    False := by
  classical
  let C := quads (starBlocks G)
  have hD := starBlocks_pairDesign hG hm
  have ⟨h4,_⟩ := deficit_le_two_local_classification hD hDeg
  by_cases hQ : C.Nonempty
  · obtain ⟨Q,hQm⟩ := hQ
    obtain ⟨hQB,hQc⟩ := Finset.mem_filter.mp hQm
    have hQS := (hD.1 Q hQB).1
    have hSQ : sources G = Q := by
      symm
      apply Finset.eq_of_subset_of_card_le hQS
      omega
    have hQuad : C = {Q} := by
      ext T
      constructor
      · intro hT
        obtain ⟨hTB,hTc⟩ := Finset.mem_filter.mp hT
        have hTS : T ⊆ Q := by rw [← hSQ]; exact (hD.1 T hTB).1
        exact Finset.mem_singleton.mpr (Finset.eq_of_subset_of_card_le hTS (by omega))
      · intro hT
        exact (Finset.mem_singleton.mp hT).symm ▸ hQm
    have hTr : triples (starBlocks G) = ∅ := by
      by_contra hn
      obtain ⟨T,hT⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      obtain ⟨hTB,hTc⟩ := Finset.mem_filter.mp hT
      have hNe : T ≠ Q := by intro he; rw [he] at hTc; omega
      have hDis := (quad_disjoint_nonpair_and_exact_deficit hD hDeg hQm).1 T hTB
        (by omega) hNe
      obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
      have hvS := (hD.1 T hTB).1 hv
      exact (Finset.disjoint_left.mp hDis) (hSQ ▸ hvS) hv
    exact exact_four_deficit_le_two_not_sole_quad hG hm hI hDeg hQuad hTr
  · have hEmpty : C = ∅ := by
      by_contra hn
      exact hQ (Finset.nonempty_iff_ne_empty.mpr hn)
    have ht := triples_card_le_one_of_support_le_four hD hsmall
    have hDegOne : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2 := by
      intro v hv
      have hLocal := designDegree_add_triple_quad hD h4 hv
      have hT : tripleDegree (starBlocks G) v ≤ 1 := by
        unfold tripleDegree
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans ht
      have hQzero : quadDegree (starBlocks G) v = 0 := by
        unfold quadDegree
        change (C.filter (v ∈ ·)).card = 0
        simp [hEmpty]
      omega
    exact exact_four_not_multiple_sources_of_deficit_le_one hG hm hI hk hDegOne

#print axioms exact_four_deficit_le_two_not_sole_quad
#print axioms triples_card_le_one_of_support_le_four
#print axioms exact_four_deficit_le_two_not_small_sources
end FranklForcingFiber
