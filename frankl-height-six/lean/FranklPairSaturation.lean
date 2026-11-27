import FranklCrossStarPair

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- If the pair fiber beats the height-three bound on one fewer coordinate,
every available representative is present in its compressed support. -/
theorem cross_pair_support_saturated {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t)
    (hlarge : 1 + ((pairReps G p q).card - 1) + Nat.choose ((pairReps G p q).card - 1) 2 <
      (avoidBoth G s t).card) :
    ground (compressPair G p q s t) = pairReps G p q := by
  have hsub := compressPair_ground_subset_reps (G := G) (p := p) (q := q) (s := s) (t := t)
  by_contra hne
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hr : (ground (compressPair G p q s t)).card ≤ (pairReps G p q).card - 1 := by omega
  have hc := Nat.choose_le_choose 2 hr
  have h4 := cross_pair_compress_noFourChain hG hmin hp hq hpq hps hqt hf hg
    (cross_pair_noFourChain hG hmin hp hq hpq hps hqt hf hg)
  have hu := FranklHeightThreeSauer.card_le (ground (compressPair G p q s t))
    (compress_pair_unionClosed hG.2.2.1) h4 (fun _ hA => subset_ground hA)
  have he := cross_pair_compress_card hG hmin hp hq hpq hps hqt hf hg
  omega

/-- It is enough for the canonical lower bound alone to exceed the
height-three bound on one fewer representative. -/
theorem cross_pair_support_saturated_of_ground {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t)
    (hlarge : 1 + ((pairReps G p q).card - 1) + Nat.choose ((pairReps G p q).card - 1) 2 <
      (ground G).card - 1) :
    ground (compressPair G p q s t) = pairReps G p q := by
  obtain ⟨hs, ht, hts, _, hsT, htT⟩ := cross_pair_terminal_data hG hmin hp hq hpq hps hqt hf hg
  have hn := terminal_pair_avoidance_card hG (weakMinimalGround_separated hG hmin) hs ht hts hsT htT
  exact cross_pair_support_saturated hG hmin hp hq hpq hps hqt hf hg (by omega)

theorem mem_raw_ground_of_mem_compress_ground {G : Finset (Finset α)} {p q s t x : α}
    (hx : x ∈ ground (compressPair G p q s t)) : x ∈ ground (avoidBoth G s t) := by
  obtain ⟨B, hB, hxB⟩ := exists_mem_of_mem_ground hx
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
  exact subset_ground hA (Finset.mem_inter.mp hxB).1

/-- Without saturation the pair maximum still contains no point of either
selected star, including the two sources. -/
theorem cross_pair_top_mem_outside_of_mem {G : Finset (Finset α)} {p q s t x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t)
    (hx : x ∈ ground (avoidBoth G s t)) :
    x ∈ ground G ∧ x ≠ p ∧ x ≠ q ∧ ¬ Forces G p x ∧ ¬ Forces G q x := by
  obtain ⟨A, hA, hxA⟩ := exists_mem_of_mem_ground hx
  obtain ⟨hAG, hst⟩ := Finset.mem_filter.mp hA
  have hAs : s ∉ A := fun h => hst (Or.inl h)
  have hAt : t ∉ A := fun h => hst (Or.inr h)
  have hAp : p ∉ A := fun h => hAs (hf hAG h)
  have hAq : q ∉ A := fun h => hAt (hg hAG h)
  have hxp : x ≠ p := fun e => hAp (e ▸ hxA)
  have hxq : x ≠ q := fun e => hAq (e ▸ hxA)
  refine ⟨subset_ground hAG hxA, hxp, hxq, ?_, ?_⟩
  · intro hpx
    have hloc := local_twins_across_stars hG hmin hq hp hqt hxp.symm hpq.symm hg hpx hAG hAt
    exact hAp (hloc.mpr hxA)
  · intro hqx
    have hloc := local_twins_across_stars hG hmin hp hq hps hxq.symm hpq hf hqx hAG hAs
    exact hAq (hloc.mpr hxA)

/-- With full compressed support, the raw maximum is exactly the ground with
the two selected stars removed. -/
theorem cross_pair_top_exact_of_support {G : Finset (Finset α)} {p q s t x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t)
    (hfull : ground (compressPair G p q s t) = pairReps G p q) :
    x ∈ ground (avoidBoth G s t) ↔
      x ∈ ground G ∧ x ≠ p ∧ x ≠ q ∧ ¬ Forces G p x ∧ ¬ Forces G q x := by
  classical
  refine ⟨cross_pair_top_mem_outside_of_mem hG hmin hp hq hpq hps hqt hf hg, ?_⟩
  intro hx
  obtain ⟨hxG, hxp, hxq, hfpx, hfqx⟩ := hx
  have hsep := weakMinimalGround_separated hG hmin
  by_cases hleaf : x ∈ leaves G
  · obtain ⟨y, hy, hyx, hfy⟩ := (mem_leaves.mp hleaf).2
    have hyp : y ≠ p := fun e => hfpx (e ▸ hfy)
    have hyq : y ≠ q := fun e => hfqx (e ▸ hfy)
    have hyR : y ∈ pairReps G p q :=
      mem_pairReps.mpr ⟨hy, outgoing_not_leaf hG hsep hyx hfy, hyp, hyq⟩
    have hyC : y ∈ ground (compressPair G p q s t) := hfull.symm ▸ hyR
    have hyN := mem_raw_ground_of_mem_compress_ground hyC
    obtain ⟨A, ha, hyA⟩ := exists_mem_of_mem_ground hyN
    exact subset_ground ha (hfy (Finset.mem_filter.mp ha).1 hyA)
  · have hxR : x ∈ pairReps G p q := mem_pairReps.mpr ⟨hxG, hleaf, hxp, hxq⟩
    exact mem_raw_ground_of_mem_compress_ground (hfull.symm ▸ hxR)

/-- The fully quantified exact maximum follows directly from the numerical
saturation test on the canonical count. -/
theorem cross_pair_top_exact_of_ground_bound {G : Finset (Finset α)} {p q s t x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t)
    (hlarge : 1 + ((pairReps G p q).card - 1) + Nat.choose ((pairReps G p q).card - 1) 2 <
      (ground G).card - 1) :
    x ∈ ground (avoidBoth G s t) ↔
      x ∈ ground G ∧ x ≠ p ∧ x ≠ q ∧ ¬ Forces G p x ∧ ¬ Forces G q x :=
  cross_pair_top_exact_of_support hG hmin hp hq hpq hps hqt hf hg
    (cross_pair_support_saturated_of_ground hG hmin hp hq hpq hps hqt hf hg hlarge)

/-- A pair fiber is independent of which leaves were chosen from its two stars. -/
theorem cross_pair_independent_of_leaves {G : Finset (Finset α)} {p q s t u v : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hpu : p ≠ u) (hqv : q ≠ v)
    (hf : Forces G p s) (hg : Forces G q t) (hi : Forces G p u) (hj : Forces G q v) :
    avoidBoth G s t = avoidBoth G u v := by
  have haux {a b c d : α} (hpa : p ≠ a) (hqb : q ≠ b) (hpc : p ≠ c) (hqd : q ≠ d)
      (fa : Forces G p a) (fb : Forces G q b) (fc : Forces G p c) (fd : Forces G q d) :
      avoidBoth G a b ⊆ avoidBoth G c d := by
    intro A hA
    obtain ⟨hAG, hab⟩ := Finset.mem_filter.mp hA
    have ha : a ∉ A := fun h => hab (Or.inl h)
    have hb : b ∉ A := fun h => hab (Or.inr h)
    have hpn : p ∉ A := fun h => ha (fa hAG h)
    have hqn : q ∉ A := fun h => hb (fb hAG h)
    have hc := local_twins_across_stars hG hmin hq hp hqb hpc hpq.symm fb fc hAG hb
    have hd := local_twins_across_stars hG hmin hp hq hpa hqd hpq fa fd hAG ha
    exact Finset.mem_filter.mpr ⟨hAG, fun h => h.elim (fun h' => hpn (hc.mpr h')) (fun h' => hqn (hd.mpr h'))⟩
  exact Finset.Subset.antisymm (haux hps hqt hpu hqv hf hg hi hj) (haux hpu hqv hps hqt hi hj hf hg)

#print axioms cross_pair_support_saturated
#print axioms cross_pair_top_exact_of_ground_bound
#print axioms cross_pair_independent_of_leaves

end FranklForcingFiber
