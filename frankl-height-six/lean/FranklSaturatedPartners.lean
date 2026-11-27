import FranklPairSaturation

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

theorem cross_pair_avoidBoth_nonempty {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t) :
    (avoidBoth G s t).Nonempty := by
  obtain ⟨hs, ht, hts, _, hsT, htT⟩ := cross_pair_terminal_data hG hmin hp hq hpq hps hqt hf hg
  have hn := terminal_pair_avoidance_card hG (weakMinimalGround_separated hG hmin) hs ht hts hsT htT
  have hC1 := Finset.card_erase_add_one hs
  have hC2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hts, ht⟩)
  exact Finset.card_pos.mp (by omega)

/-- A center with two different fully supported pair fibers has only one
leaf. Otherwise unioning the two pair maxima creates a forbidden extra rank. -/
theorem center_unary_of_two_saturated_partners {G : Finset (Finset α)} {p q r s t v : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hr : r ∈ ground G)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hps : p ≠ s) (hqt : q ≠ t) (hrv : r ≠ v)
    (hFp : Forces G p s) (hFq : Forces G q t) (hFr : Forces G r v)
    (hfullq : ground (compressPair G p q s t) = pairReps G p q)
    (hfullr : ground (compressPair G p r s v) = pairReps G p r) :
    ∀ ⦃u⦄, p ≠ u → Forces G p u → u = s := by
  intro u hpu hFu
  by_contra hus
  have hsep := weakMinimalGround_separated hG hmin
  obtain ⟨hs, ht, hts, htp, hsT, htT⟩ := cross_pair_terminal_data hG hmin hp hq hpq hps hqt hFp hFq
  let Tq := ground (avoidBoth G s t)
  let Tr := ground (avoidBoth G s v)
  let X := Tq ∪ Tr
  have hTq : Tq ∈ G := avoidBoth_top_mem hG (cross_pair_avoidBoth_nonempty hG hmin hp hq hpq hps hqt hFp hFq)
  have hTr : Tr ∈ G := avoidBoth_top_mem hG (cross_pair_avoidBoth_nonempty hG hmin hp hr hpr hps hrv hFp hFr)
  have hX : X ∈ G := hG.2.2.1 hTq hTr
  have hnot_q_p : ¬ Forces G p q := fun h => noThreeForcingChain_of_separated hG hsep hp hpq hqt h hFq
  have hnot_q_r : ¬ Forces G r q := fun h => noThreeForcingChain_of_separated hG hsep hr hqr.symm hqt h hFq
  have hqTr : q ∈ Tr := (cross_pair_top_exact_of_support hG hmin hp hr hpr hps hrv hFp hFr hfullr).mpr
    ⟨hq, hpq.symm, hqr, hnot_q_p, hnot_q_r⟩
  have hqTq : q ∉ Tq := fun h =>
    (cross_pair_top_exact_of_support hG hmin hp hq hpq hps hqt hFp hFq hfullq).mp h |>.2.2.1 rfl
  have h1 : Tq ⊂ X := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_union_left, fun e => hqTq (e.symm ▸ Finset.mem_union_right Tq hqTr)⟩
  have huTq : u ∉ Tq := fun h =>
    (cross_pair_top_exact_of_support hG hmin hp hq hpq hps hqt hFp hFq hfullq).mp h |>.2.2.2.1 hFu
  have huTr : u ∉ Tr := fun h =>
    (cross_pair_top_exact_of_support hG hmin hp hr hpr hps hrv hFp hFr hfullr).mp h |>.2.2.2.1 hFu
  have huCs : u ∈ avoid G s := by
    rw [avoid_eq_coPair_of_edge hG hmin hp hps hFp]
    exact Finset.mem_erase.mpr ⟨hus, Finset.mem_erase.mpr ⟨hpu.symm, mem_ground_of_forces hp hFu⟩⟩
  have hsX : s ∉ X := fun h => (Finset.mem_union.mp h).elim
    (notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G s)))
    (notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G s)))
  have h2 : X ⊂ avoid G s := Finset.ssubset_iff_subset_ne.mpr
    ⟨avoid_subset hX hsX, fun e => by
      have huX : u ∈ X := e.symm ▸ huCs
      exact (Finset.mem_union.mp huX).elim huTq huTr⟩
  have h3 : avoid G s ⊂ (ground G).erase p := by
    rw [avoid_eq_coPair_of_edge hG hmin hp hps hFp]
    exact Finset.erase_ssubset (Finset.mem_erase.mpr ⟨hps.symm, hs⟩)
  exact terminal_pair_top_noFiveChain hG hsep hs ht hp hts hps htp.symm hsT htT hFp
    hX (avoid_mem_weak hG s) (coSingleton_of_outgoing hG hsep hp hps hFp) (ground_mem_weak hG)
    h1 h2 h3 (Finset.erase_ssubset hp)

/-- Uniform numerical saturation is a sufficient condition for the preceding
two-partner restriction, since any actual pair fiber is at least m−1 large
where m is the ground cardinality. -/
theorem center_unary_of_two_numerically_saturated_partners {G : Finset (Finset α)}
    {p q r s t v : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hr : r ∈ ground G)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hps : p ≠ s) (hqt : q ≠ t) (hrv : r ≠ v)
    (hFp : Forces G p s) (hFq : Forces G q t) (hFr : Forces G r v)
    (hqLarge : 1 + ((pairReps G p q).card - 1) + Nat.choose ((pairReps G p q).card - 1) 2 <
      (ground G).card - 1)
    (hrLarge : 1 + ((pairReps G p r).card - 1) + Nat.choose ((pairReps G p r).card - 1) 2 <
      (ground G).card - 1) :
    ∀ ⦃u⦄, p ≠ u → Forces G p u → u = s :=
  center_unary_of_two_saturated_partners hG hmin hp hq hr hpq hpr hqr hps hqt hrv hFp hFq hFr
    (cross_pair_support_saturated_of_ground hG hmin hp hq hpq hps hqt hFp hFq hqLarge)
    (cross_pair_support_saturated_of_ground hG hmin hp hr hpr hps hrv hFp hFr hrLarge)

#print axioms center_unary_of_two_saturated_partners
#print axioms center_unary_of_two_numerically_saturated_partners

end FranklForcingFiber
