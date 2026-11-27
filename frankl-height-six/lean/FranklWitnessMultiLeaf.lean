import FranklWitnessCounting

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- A pair anchored at a multi-leaf star only uses isolates, yet the new
witness count supplies one extra set for each center. -/
theorem multileaf_center_isolated_bound_with_sources {G : Finset (Finset α)}
    {p q s t u : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hpu : p ≠ u) (hus : u ≠ s)
    (hFp : Forces G p s) (hFq : Forces G q t) (hFu : Forces G p u) :
    (ground G).card + (sources G).card ≤ 2 + (isolated G).card + Nat.choose (isolated G).card 2 := by
  obtain ⟨hsG,htG,hts,_,_,_⟩ := cross_pair_terminal_data hG hmin hp hq hpq hps hqt hFp hFq
  have hsL : s ∈ leaves G := mem_leaves.mpr ⟨hsG,p,hp,hps,hFp⟩
  have htL : t ∈ leaves G := mem_leaves.mpr ⟨htG,q,hq,hqt,hFq⟩
  have hN := leaf_pair_avoidance_extra_witnesses hG hmin hsL htL hts
  have hi := cross_pair_top_subset_isolated_of_multileaf hG hmin hp hq hpq hps hqt hpu hus hFp hFq hFu
  have hb := FranklHeightThreeSauer.card_le (isolated G)
    (cross_pair_unionClosed (s := s) (t := t) hG.2.2.1)
    (cross_pair_noFourChain hG hmin hp hq hpq hps hqt hFp hFq)
    (fun _ hA => (subset_ground hA).trans hi)
  omega

/-- A nonunary star together with another nontrivial star requires at least
four isolated points. -/
theorem multileaf_center_four_isolated {G : Finset (Finset α)}
    {p q s t u : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hpu : p ≠ u) (hus : u ≠ s)
    (hFp : Forces G p s) (hFq : Forces G q t) (hFu : Forces G p u) :
    4 ≤ (isolated G).card := by
  have hk : 1 < (sources G).card := Finset.one_lt_card_iff.mpr
    ⟨p,q,mem_sources.mpr ⟨hp,s,hps,hFp⟩,mem_sources.mpr ⟨hq,t,hqt,hFq⟩,hpq⟩
  have hst : s ≠ t := by
    intro he
    subst t
    exact hpq (weakMinimalGround_unique_proper_predecessor hG hmin hp hq hps hqt hFp hFq)
  have htu : t ≠ u := by
    intro he
    subst t
    exact hpq (weakMinimalGround_unique_proper_predecessor hG hmin hp hq hpu hqt hFu hFq)
  have hL : 2 < (leaves G).card := Finset.two_lt_card_iff.mpr
    ⟨s,t,u,mem_leaves.mpr ⟨mem_ground_of_forces hp hFp,p,hp,hps,hFp⟩,
      mem_leaves.mpr ⟨mem_ground_of_forces hq hFq,q,hq,hqt,hFq⟩,
      mem_leaves.mpr ⟨mem_ground_of_forces hp hFu,p,hp,hpu,hFu⟩,hst,hus.symm,htu⟩
  have hn := partition_card hG hmin
  have hb := multileaf_center_isolated_bound_with_sources hG hmin hp hq hpq hps hqt hpu hus hFp hFq hFu
  by_contra! hi
  have hc : (isolated G).card.choose 2 ≤ 3 :=
    (Nat.choose_le_choose 2 (show (isolated G).card ≤ 3 by omega)).trans (by decide)
  omega

#print axioms multileaf_center_isolated_bound_with_sources
#print axioms multileaf_center_four_isolated

end FranklForcingFiber
