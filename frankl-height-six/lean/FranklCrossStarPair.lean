import FranklForcingFiber
import FranklHeightThreeSauer

namespace FranklForcingFiber

variable {α : Type*} [DecidableEq α]

/-- A family of height at most three has no four-member strict chain. -/
def NoFourChain (L : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C D⦄, A ∈ L → B ∈ L → C ∈ L → D ∈ L →
    A ⊂ B → B ⊂ C → C ⊂ D → False

def IsLeaf (G : Finset (Finset α)) (x : α) : Prop :=
  ∃ p ∈ ground G, p ≠ x ∧ Forces G p x

noncomputable def leaves (G : Finset (Finset α)) : Finset α := by
  classical
  exact (ground G).filter (IsLeaf G)

/-- The cross-star pair fiber retains all isolated points and all sources other
than the two sources whose leaves are being avoided. -/
noncomputable def pairReps (G : Finset (Finset α)) (p q : α) : Finset α :=
  ((ground G \ leaves G).erase p).erase q

noncomputable def compressPair (G : Finset (Finset α)) (p q s t : α) : Finset (Finset α) :=
  (avoidBoth G s t).image (fun A => A ∩ pairReps G p q)

theorem mem_leaves {G : Finset (Finset α)} {x : α} :
    x ∈ leaves G ↔ x ∈ ground G ∧ IsLeaf G x := by
  classical
  exact Finset.mem_filter

theorem mem_pairReps {G : Finset (Finset α)} {x p q : α} :
    x ∈ pairReps G p q ↔ x ∈ ground G ∧ x ∉ leaves G ∧ x ≠ p ∧ x ≠ q := by
  simp only [pairReps, Finset.mem_erase, Finset.mem_sdiff]
  tauto

theorem outgoing_not_leaf {G : Finset (Finset α)} {p s : α}
    (hG : NoStrictMajority G) (hsep : Separated G)
    (hps : p ≠ s) (hf : Forces G p s) : p ∉ leaves G := by
  intro hp
  obtain ⟨x, hx, hxp, hFx⟩ := (mem_leaves.mp hp).2
  exact noThreeForcingChain_of_separated hG hsep hx hxp hps hFx hf

theorem pairReps_card_add_leaves_add_two {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hsep : Separated G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t) :
    (pairReps G p q).card + (leaves G).card + 2 = (ground G).card := by
  let R := ground G \ leaves G
  have hL : leaves G ⊆ ground G := fun _ hx => (mem_leaves.mp hx).1
  have hcap := Finset.card_sdiff_add_card_eq_card hL
  change R.card + (leaves G).card = (ground G).card at hcap
  have hpR : p ∈ R := Finset.mem_sdiff.mpr ⟨hp, outgoing_not_leaf hG hsep hps hf⟩
  have hqR : q ∈ R := Finset.mem_sdiff.mpr ⟨hq, outgoing_not_leaf hG hsep hqt hg⟩
  have hR1 := Finset.card_erase_add_one hpR
  have hR2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hpq.symm, hqR⟩)
  change (pairReps G p q).card + 1 = (R.erase p).card at hR2
  omega

theorem cross_pair_terminal_data {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t) :
    s ∈ ground G ∧ t ∈ ground G ∧ t ≠ s ∧ t ≠ p ∧ Terminal G s ∧ Terminal G t := by
  have hsep := weakMinimalGround_separated hG hmin
  have hs : Terminal G s := by
    intro x hF
    by_contra hn
    exact noThreeForcingChain_of_separated hG hsep hp hps (Ne.symm hn) hf hF
  have ht : Terminal G t := by
    intro x hF
    by_contra hn
    exact noThreeForcingChain_of_separated hG hsep hq hqt (Ne.symm hn) hg hF
  refine ⟨mem_ground_of_forces hp hf, mem_ground_of_forces hq hg, ?_, ?_, hs, ht⟩
  · intro e
    subst t
    exact hpq (weakMinimalGround_unique_proper_predecessor hG hmin hp hq hps hqt hf hg)
  · intro e
    subst t
    exact hps (ht hf).symm

theorem cross_pair_noFourChain {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hF : Forces G p s) (hg : Forces G q t) :
    NoFourChain (avoidBoth G s t) := by
  have hsep := weakMinimalGround_separated hG hmin
  obtain ⟨_, ht, hts, htp, _, _⟩ := cross_pair_terminal_data hG hmin hp hq hpq hps hqt hF hg
  have htC : t ∈ avoid G s := by
    rw [avoid_eq_coPair_of_edge hG hmin hp hps hF]
    exact Finset.mem_erase.mpr ⟨hts, Finset.mem_erase.mpr ⟨htp, ht⟩⟩
  intro A B C D ha hb hc hd hab hbc hcd
  have hd' := Finset.mem_filter.mp hd
  have hds : D ⊆ avoid G s := avoid_subset hd'.1 (fun h => hd'.2 (Or.inl h))
  have hDlt : D ⊂ avoid G s := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hds, ?_⟩
    intro he
    exact hd'.2 (Or.inr (he.symm ▸ htC))
  have htop := ground_mem_weak hG
  have hCo := coSingleton_of_outgoing hG hsep hp hps hF
  have hmid : avoid G s ⊂ (ground G).erase p := by
    rw [avoid_eq_coPair_of_edge hG hmin hp hps hF]
    exact Finset.erase_ssubset (Finset.mem_erase.mpr ⟨hps.symm, mem_ground_of_forces hp hF⟩)
  exact hG.2.2.2.1 (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
    (Finset.mem_filter.mp hc).1 hd'.1 (avoid_mem_weak hG s) hCo htop
    hab hbc hcd hDlt hmid (Finset.erase_ssubset hp)

theorem cross_pair_compress_reflect {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t)
    {A B : Finset α} (ha : A ∈ avoidBoth G s t) (hb : B ∈ avoidBoth G s t)
    (hsub : A ∩ pairReps G p q ⊆ B ∩ pairReps G p q) : A ⊆ B := by
  classical
  have hsep := weakMinimalGround_separated hG hmin
  obtain ⟨haG, hAst⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbG, _⟩ := Finset.mem_filter.mp hb
  have hAs : s ∉ A := fun h => hAst (Or.inl h)
  have hAt : t ∉ A := fun h => hAst (Or.inr h)
  intro x hx
  have hxG := subset_ground haG hx
  have hxp : x ≠ p := fun e => hAs (hf haG (e ▸ hx))
  have hxq : x ≠ q := fun e => hAt (hg haG (e ▸ hx))
  by_cases hleaf : x ∈ leaves G
  · obtain ⟨y, hy, hyx, hFy⟩ := (mem_leaves.mp hleaf).2
    have hyp : y ≠ p := by
      intro e
      subst y
      have h := local_twins_across_stars hG hmin hq hp hqt hyx hpq.symm hg hFy haG hAt
      exact hAs (hf haG (h.mpr hx))
    have hyq : y ≠ q := by
      intro e
      subst y
      have h := local_twins_across_stars hG hmin hp hq hps hyx hpq hf hFy haG hAs
      exact hAt (hg haG (h.mpr hx))
    have hPy : y ∈ pairReps G p q := mem_pairReps.mpr
      ⟨hy, outgoing_not_leaf hG hsep hyx hFy, hyp, hyq⟩
    have hlocal := local_twins_across_stars hG hmin hp hy hps hyx hyp.symm hf hFy haG hAs
    have hyA := hlocal.mpr hx
    have hyB := (Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨hyA, hPy⟩))).1
    exact hFy hbG hyB
  · have hPx : x ∈ pairReps G p q := mem_pairReps.mpr ⟨hxG, hleaf, hxp, hxq⟩
    exact (Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨hx, hPx⟩))).1

theorem cross_pair_compress_card {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t) :
    (compressPair G p q s t).card = (avoidBoth G s t).card := by
  apply Finset.card_image_of_injOn
  intro A ha B hb he
  change A ∩ pairReps G p q = B ∩ pairReps G p q at he
  exact Finset.Subset.antisymm
    (cross_pair_compress_reflect hG hmin hp hq hpq hps hqt hf hg ha hb (he ▸ Finset.Subset.rfl))
    (cross_pair_compress_reflect hG hmin hp hq hpq hps hqt hf hg hb ha (he.symm ▸ Finset.Subset.rfl))

theorem compressPair_subset_reps {G : Finset (Finset α)} {p q s t : α} {A : Finset α}
    (ha : A ∈ compressPair G p q s t) : A ⊆ pairReps G p q := by
  obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.inter_subset_right

theorem cross_pair_compress_noFourChain {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t)
    (hbase : NoFourChain (avoidBoth G s t)) : NoFourChain (compressPair G p q s t) := by
  intro A B C D ha hb hc hd hab hbc hcd
  obtain ⟨A', ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B', hb', rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨C', hc', rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨D', hd', rfl⟩ := Finset.mem_image.mp hd
  have haux {X Y : Finset α} (hx : X ∈ avoidBoth G s t) (hy : Y ∈ avoidBoth G s t)
      (hs : X ∩ pairReps G p q ⊂ Y ∩ pairReps G p q) : X ⊂ Y := by
    obtain ⟨hsub, hneq⟩ := Finset.ssubset_iff_subset_ne.mp hs
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨cross_pair_compress_reflect hG hmin hp hq hpq hps hqt hf hg hx hy hsub,
        fun e => hneq (congrArg (· ∩ pairReps G p q) e)⟩
  exact hbase ha' hb' hc' hd' (haux ha' hb' hab) (haux hb' hc' hbc) (haux hc' hd' hcd)

theorem cross_pair_unionClosed {G : Finset (Finset α)} {s t : α}
    (hG : UnionClosed G) : UnionClosed (avoidBoth G s t) := by
  intro A B ha hb
  obtain ⟨haG, hAn⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbG, hBn⟩ := Finset.mem_filter.mp hb
  refine Finset.mem_filter.mpr ⟨hG haG hbG, ?_⟩
  intro hh
  rcases hh with hs | ht
  · exact (Finset.mem_union.mp hs).elim (fun h => hAn (Or.inl h)) (fun h => hBn (Or.inl h))
  · exact (Finset.mem_union.mp ht).elim (fun h => hAn (Or.inr h)) (fun h => hBn (Or.inr h))

theorem compress_pair_unionClosed {G : Finset (Finset α)} {p q s t : α}
    (hG : UnionClosed G) : UnionClosed (compressPair G p q s t) := by
  intro A B ha hb
  obtain ⟨A', ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B', hb', rfl⟩ := Finset.mem_image.mp hb
  refine Finset.mem_image.mpr ⟨A' ∪ B', cross_pair_unionClosed hG ha' hb', ?_⟩
  ext x
  simp only [Finset.mem_union, Finset.mem_inter]
  tauto

theorem compressPair_ground_subset_reps {G : Finset (Finset α)} {p q s t : α} :
    ground (compressPair G p q s t) ⊆ pairReps G p q := by
  apply Finset.sup_le
  intro A ha
  exact compressPair_subset_reps ha

/-- The actual support of the compressed fiber yields a refinement: missing
representatives cost one unit each in addition to the leaf count. -/
theorem cross_pair_actual_support_bound {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t) :
    (pairReps G p q).card + (leaves G).card ≤
      (ground (compressPair G p q s t)).card +
      Nat.choose (ground (compressPair G p q s t)).card 2 := by
  have hsep := weakMinimalGround_separated hG hmin
  obtain ⟨hs, ht, hts, _, hsTerm, htTerm⟩ := cross_pair_terminal_data hG hmin hp hq hpq hps hqt hf hg
  have hN := terminal_pair_avoidance_card hG hsep hs ht hts hsTerm htTerm
  have hD := pairReps_card_add_leaves_add_two hG hsep hp hq hpq hps hqt hf hg
  have hC := cross_pair_compress_card hG hmin hp hq hpq hps hqt hf hg
  have h4 := cross_pair_compress_noFourChain hG hmin hp hq hpq hps hqt hf hg
    (cross_pair_noFourChain hG hmin hp hq hpq hps hqt hf hg)
  have hbound := FranklHeightThreeSauer.card_le (ground (compressPair G p q s t))
    (compress_pair_unionClosed hG.2.2.1) h4 (fun _ hA => subset_ground hA)
  omega

/-- In a weak ground-minimal counterexample with distinct nontrivial stars,
the number of leaves is at most the number of pairs of retained representatives. -/
theorem cross_pair_leaf_bound {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t) :
    (leaves G).card ≤ Nat.choose (pairReps G p q).card 2 := by
  have h := cross_pair_actual_support_bound hG hmin hp hq hpq hps hqt hf hg
  have hr := Finset.card_le_card (compressPair_ground_subset_reps (G := G) (p := p) (q := q) (s := s) (t := t))
  have hc := Nat.choose_le_choose 2 hr
  omega

#print axioms cross_pair_noFourChain
#print axioms cross_pair_compress_reflect
#print axioms cross_pair_compress_card
#print axioms cross_pair_compress_noFourChain
#print axioms pairReps_card_add_leaves_add_two
#print axioms compress_pair_unionClosed
#print axioms cross_pair_actual_support_bound
#print axioms cross_pair_leaf_bound

end FranklForcingFiber
