import FranklSaturatedPartners
import FranklStarIndex

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- Fix the first center and a leaf from it. If it has another leaf, every
partner gives the same pair maximum, even without support saturation. -/
theorem cross_pair_top_constant_of_multileaf {G : Finset (Finset α)}
    {p q r s t v u : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hr : r ∈ ground G)
    (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hqt : q ≠ t) (hrv : r ≠ v) (hpu : p ≠ u) (hus : u ≠ s)
    (hFp : Forces G p s) (hFq : Forces G q t) (hFr : Forces G r v) (hFu : Forces G p u) :
    ground (avoidBoth G s t) = ground (avoidBoth G s v) := by
  have hsep := weakMinimalGround_separated hG hmin
  have hhelper {b c y z : α} (hb : b ∈ ground G) (hc : c ∈ ground G)
      (hpb : p ≠ b) (hpc : p ≠ c) (hby : b ≠ y) (hcz : c ≠ z)
      (hFb : Forces G b y) (hFc : Forces G c z) :
      ground (avoidBoth G s z) ⊆ ground (avoidBoth G s y) := by
    obtain ⟨hs, hy, hys, hyp, hsT, hyT⟩ := cross_pair_terminal_data hG hmin hp hb hpb hps hby hFp hFb
    let Ty := ground (avoidBoth G s y)
    let Tz := ground (avoidBoth G s z)
    let X := Ty ∪ Tz
    have hTy : Ty ∈ G := avoidBoth_top_mem hG
      (cross_pair_avoidBoth_nonempty hG hmin hp hb hpb hps hby hFp hFb)
    have hTz : Tz ∈ G := avoidBoth_top_mem hG
      (cross_pair_avoidBoth_nonempty hG hmin hp hc hpc hps hcz hFp hFc)
    have hX : X ∈ G := hG.2.2.1 hTy hTz
    intro x hx
    by_contra hnx
    have h1 : Ty ⊂ X := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_union_left, fun e => by
        have hxX : x ∈ X := Finset.mem_union_right Ty hx
        exact hnx (show x ∈ Ty from e.symm ▸ hxX)⟩
    have huTy : u ∉ Ty := fun h =>
      (cross_pair_top_mem_outside_of_mem hG hmin hp hb hpb hps hby hFp hFb h).2.2.2.1 hFu
    have huTz : u ∉ Tz := fun h =>
      (cross_pair_top_mem_outside_of_mem hG hmin hp hc hpc hps hcz hFp hFc h).2.2.2.1 hFu
    have huCs : u ∈ avoid G s := by
      rw [avoid_eq_coPair_of_edge hG hmin hp hps hFp]
      exact Finset.mem_erase.mpr ⟨hus, Finset.mem_erase.mpr ⟨hpu.symm, mem_ground_of_forces hp hFu⟩⟩
    have hsX : s ∉ X := fun h => (Finset.mem_union.mp h).elim
      (notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G s)))
      (notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G s)))
    have h2 : X ⊂ avoid G s := Finset.ssubset_iff_subset_ne.mpr
      ⟨avoid_subset hX hsX, fun e => by
        have huX : u ∈ X := e.symm ▸ huCs
        exact (Finset.mem_union.mp huX).elim huTy huTz⟩
    have h3 : avoid G s ⊂ (ground G).erase p := by
      rw [avoid_eq_coPair_of_edge hG hmin hp hps hFp]
      exact Finset.erase_ssubset (Finset.mem_erase.mpr ⟨hps.symm, hs⟩)
    exact terminal_pair_top_noFiveChain hG hsep hs hy hp hys hps hyp.symm hsT hyT hFp
      hX (avoid_mem_weak hG s) (coSingleton_of_outgoing hG hsep hp hps hFp) (ground_mem_weak hG)
      h1 h2 h3 (Finset.erase_ssubset hp)
  exact Finset.Subset.antisymm (hhelper hr hq hpr hpq hrv hqt hFr hFq)
    (hhelper hq hr hpq hpr hqt hrv hFq hFr)

theorem mem_isolated {G : Finset (Finset α)} {x : α} :
    x ∈ isolated G ↔ x ∈ ground G ∧ Terminal G x ∧ x ∉ leaves G := by
  classical
  simp only [isolated,Finset.mem_sdiff,mem_sources,Terminal]
  constructor
  · rintro ⟨⟨hg,hl⟩,hn⟩
    refine ⟨hg,?_ ,hl⟩
    intro y hf
    by_contra hy
    exact hn ⟨hg,y,fun h => hy h.symm,hf⟩
  · rintro ⟨hg,ht,hl⟩
    exact ⟨⟨hg,hl⟩,fun h => by obtain ⟨_,y,hne,hf⟩ := h; exact hne (ht hf).symm⟩

/-- If one selected center has at least two leaves, the entire pair fiber
uses only isolated points, no matter how many other stars there are. -/
theorem cross_pair_top_subset_isolated_of_multileaf {G : Finset (Finset α)}
    {p q s t u : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hpu : p ≠ u) (hus : u ≠ s)
    (hFp : Forces G p s) (hFq : Forces G q t) (hFu : Forces G p u) :
    ground (avoidBoth G s t) ⊆ isolated G := by
  intro x hx
  obtain ⟨hxG, hxp, _, hpx, _⟩ := cross_pair_top_mem_outside_of_mem
    hG hmin hp hq hpq hps hqt hFp hFq hx
  have hno {r v : α} (hr : r ∈ ground G) (hrv : r ≠ v) (hf : Forces G r v) :
      x ≠ r ∧ ¬ Forces G r x := by
    by_cases hpr : p = r
    · subst r
      exact ⟨hxp, hpx⟩
    · have he := cross_pair_top_constant_of_multileaf hG hmin hp hq hr hpq hpr hps hqt hrv hpu hus
        hFp hFq hf hFu
      have hx' : x ∈ ground (avoidBoth G s v) := he ▸ hx
      have hh := cross_pair_top_mem_outside_of_mem hG hmin hp hr hpr hps hrv hFp hf hx'
      exact ⟨hh.2.2.1, hh.2.2.2.2⟩
  refine mem_isolated.mpr ⟨hxG, ?_, ?_⟩
  · intro v hf
    by_contra hn
    exact (hno hxG (Ne.symm hn) hf).1 rfl
  · intro hl
    obtain ⟨r, hr, hrx, hf⟩ := (mem_leaves.mp hl).2
    exact (hno hr hrx hf).2 hf

/-- If there are at least two nontrivial stars and one has two leaves,
the ground size is at most two plus the isolated count plus its pair count. -/
theorem multileaf_center_isolated_bound {G : Finset (Finset α)}
    {p q s t u : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hpu : p ≠ u) (hus : u ≠ s)
    (hFp : Forces G p s) (hFq : Forces G q t) (hFu : Forces G p u) :
    (ground G).card ≤ 2 + (isolated G).card + Nat.choose (isolated G).card 2 := by
  obtain ⟨hs, ht, hts, _, hsT, htT⟩ := cross_pair_terminal_data hG hmin hp hq hpq hps hqt hFp hFq
  have hN := terminal_pair_avoidance_card hG (weakMinimalGround_separated hG hmin) hs ht hts hsT htT
  have hi := cross_pair_top_subset_isolated_of_multileaf hG hmin hp hq hpq hps hqt hpu hus hFp hFq hFu
  have hbound := FranklHeightThreeSauer.card_le (isolated G)
    (cross_pair_unionClosed (s := s) (t := t) hG.2.2.1)
    (cross_pair_noFourChain hG hmin hp hq hpq hps hqt hFp hFq)
    (fun _ hA => (subset_ground hA).trans hi)
  omega

/-- With another nontrivial star present, a center with two leaves needs
at least three isolated points. -/
theorem multileaf_center_three_isolated {G : Finset (Finset α)}
    {p q s t u : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hpu : p ≠ u) (hus : u ≠ s)
    (hFp : Forces G p s) (hFq : Forces G q t) (hFu : Forces G p u) :
    3 ≤ (isolated G).card := by
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
  have hb := multileaf_center_isolated_bound hG hmin hp hq hpq hps hqt hpu hus hFp hFq hFu
  by_contra! hi
  have hc : (isolated G).card.choose 2 ≤ 1 :=
    (Nat.choose_le_choose 2 (show (isolated G).card ≤ 2 by omega)).trans (by decide)
  omega

#print axioms multileaf_center_three_isolated
#print axioms cross_pair_top_constant_of_multileaf
#print axioms cross_pair_top_subset_isolated_of_multileaf
#print axioms multileaf_center_isolated_bound

end FranklForcingFiber
