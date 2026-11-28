import FranklTrueComplement
import FranklOmittedStarBlocks

/- Kernel-checked on pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- The representative family anchored at the two chosen leaves. -/
noncomputable def compressedStarPair (G : Finset (Finset α)) (p q : α) :
    Finset (Finset α) :=
  compressPair G p q (starLeaf G p) (starLeaf G q)

noncomputable def starPairTrueComplement (G : Finset (Finset α)) (p q : α) :
    Finset (Finset α) :=
  trueComplement (compressedStarPair G p q)

theorem compressedStarPair_unionClosed {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) : UnionClosed (compressedStarPair G p q) :=
  compress_pair_unionClosed hG.2.2.1

theorem compressedStarPair_nonempty {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
    (compressedStarPair G p q).Nonempty := by
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  obtain ⟨A,ha⟩ := cross_pair_avoidBoth_nonempty hG hmin (mem_sources.mp hp).1
    (mem_sources.mp hq).1 hpq hps hqt hFp hFq
  exact ⟨A ∩ pairReps G p q,Finset.mem_image.mpr ⟨A,ha,rfl⟩⟩

theorem compressedStarPair_noFourChain {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
    NoFourChain (compressedStarPair G p q) := by
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  have hpG := (mem_sources.mp hp).1
  have hqG := (mem_sources.mp hq).1
  exact cross_pair_compress_noFourChain hG hmin hpG hqG hpq hps hqt hFp hFq
    (cross_pair_noFourChain hG hmin hpG hqG hpq hps hqt hFp hFq)

theorem compressedStarPair_card {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
    (compressedStarPair G p q).card = (avoidBoth G (starLeaf G p) (starLeaf G q)).card := by
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  exact cross_pair_compress_card hG hmin (mem_sources.mp hp).1 (mem_sources.mp hq).1
    hpq hps hqt hFp hFq

theorem starPairTrueComplement_card {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
    (starPairTrueComplement G p q).card = (avoidBoth G (starLeaf G p) (starLeaf G q)).card :=
  (trueComplement_card_eq _).trans (compressedStarPair_card hG hmin hp hq hpq)

/-- Compute the true support before complementing. No saturation of the
available representatives is assumed. -/
theorem compressedStarPair_ground_eq_inter (G : Finset (Finset α)) (p q : α) :
    ground (compressedStarPair G p q) = starPairMax G p q ∩ pairReps G p q := by
  ext x
  constructor
  · intro hx
    obtain ⟨B,hB,hxB⟩ := exists_mem_of_mem_ground hx
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨hxA,hxR⟩ := Finset.mem_inter.mp hxB
    exact Finset.mem_inter.mpr ⟨subset_ground hA hxA,hxR⟩
  · intro hx
    obtain ⟨hxT,hxR⟩ := Finset.mem_inter.mp hx
    obtain ⟨A,hA,hxA⟩ := exists_mem_of_mem_ground hxT
    exact subset_ground (show A ∩ pairReps G p q ∈ compressedStarPair G p q from
      Finset.mem_image.mpr ⟨A,hA,rfl⟩) (Finset.mem_inter.mpr ⟨hxA,hxR⟩)

/-- On the actual support every nonomitted source is present, and the
isolates may or may not be present. This is the precise statement needed
to distinguish a missing coordinate from two merged atoms. -/
theorem compressedStarPair_ground_eq_centers_union_present_isolates
    {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
    ground (compressedStarPair G p q) =
      (sources G \ omittedStars G (starPairMax G p q)) ∪
        (isolated G ∩ starPairMax G p q) := by
  classical
  let T := starPairMax G p q
  let B := omittedStars G T
  have hpG := (mem_sources.mp hp).1
  have hqG := (mem_sources.mp hq).1
  have hpB : p ∈ B := mem_omittedStars.mpr ⟨hp,starPairMax_omit_left G p q⟩
  have hqB : q ∈ B := mem_omittedStars.mpr ⟨hq,starPairMax_omit_right G p q⟩
  have hT : T ∈ G := starPairMax_mem_family hG hmin hp hq hpq
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  rw [compressedStarPair_ground_eq_inter]
  ext x
  constructor
  · intro hx
    obtain ⟨hxT,hxR⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxG,hxL,_,_⟩ := mem_pairReps.mp hxR
    by_cases hxS : x ∈ sources G
    · have hxB : x ∉ B := by
        intro h
        exact (mem_omittedStars.mp h).2 ((starLeaf_spec hxS).2 hT hxT)
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxS,hxB⟩)
    · have hxI : x ∈ isolated G := Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hxG,hxL⟩,hxS⟩
      exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxI,hxT⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hxS,hxB⟩ := Finset.mem_sdiff.mp hx
      have hxp : x ≠ p := fun e => hxB (e.symm ▸ hpB)
      have hxq : x ≠ q := fun e => hxB (e.symm ▸ hqB)
      have hxG := (mem_sources.mp hxS).1
      have hxL := (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin hxS)).2
      obtain ⟨hxs,hFx⟩ := starLeaf_spec hxS
      have hxLeaf : starLeaf G x ∈ T := by
        by_contra hn
        exact hxB (mem_omittedStars.mpr ⟨hxS,hn⟩)
      have htwin := local_twins_across_stars hG hmin hpG hxG hps hxs hxp.symm
        hFp hFx hT (starPairMax_omit_left G p q)
      exact Finset.mem_inter.mpr
        ⟨htwin.mpr hxLeaf,mem_pairReps.mpr ⟨hxG,hxL,hxp,hxq⟩⟩
    · obtain ⟨hxI,hxT⟩ := Finset.mem_inter.mp hx
      have hxNoS := (Finset.mem_sdiff.mp hxI).2
      obtain ⟨hxG,_,hxL⟩ := mem_isolated.mp hxI
      exact Finset.mem_inter.mpr ⟨hxT,mem_pairReps.mpr
        ⟨hxG,hxL,fun e => hxNoS (e.symm ▸ hp),fun e => hxNoS (e.symm ▸ hq)⟩⟩

/-- The three geometric hypotheses and support property for the generic
atom bound. This theorem needs neither a unary-star nor an all-pair
assumption. -/
theorem starPairTrueComplement_rankTwo {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
    (∅ : Finset α) ∈ starPairTrueComplement G p q ∧
      FranklRankTwoAtoms.InterClosed (starPairTrueComplement G p q) ∧
      FranklHeightThreeSauer.NoFourChain (starPairTrueComplement G p q) ∧
      ∀ ⦃D⦄, D ∈ starPairTrueComplement G p q → D ⊆ ground (compressedStarPair G p q) := by
  have hU := compressedStarPair_unionClosed (p := p) (q := q) hG
  exact ⟨trueComplement_empty_mem hU (compressedStarPair_nonempty hG hmin hp hq hpq),
    trueComplement_interClosed hU,
    trueComplement_noFourChain (compressedStarPair_noFourChain hG hmin hp hq hpq),
    fun _ h => mem_complementOn_subset h⟩

/-- Refined atom bound stated in the original leaf-pair fiber's cardinality. -/
theorem leafPairAvoidance_card_le_trueSupport_atoms {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤
      1 + (ground (compressedStarPair G p q)).card +
        (FranklRankTwoAtoms.atoms (starPairTrueComplement G p q)).card.choose 2 := by
  rw [← compressedStarPair_card hG hmin hp hq hpq]
  exact trueComplement_atom_bound (compressedStarPair_unionClosed hG)
    (compressedStarPair_nonempty hG hmin hp hq hpq)
    (compressedStarPair_noFourChain hG hmin hp hq hpq)

/-- An abstract rank-two relative omission has a genuine original
leaf-pair-avoiding preimage, with the stated representative trace. -/
theorem original_member_of_starPairTrueComplement
    {G : Finset (Finset α)} {p q : α} {J : Finset α}
    (hJ : J ∈ starPairTrueComplement G p q) :
    ∃ A ∈ avoidBoth G (starLeaf G p) (starLeaf G q),
      A ∩ pairReps G p q = ground (compressedStarPair G p q) \ J := by
  have hK : ground (compressedStarPair G p q) \ J ∈ compressedStarPair G p q :=
    ((complementOn_mem_iff (fun _ h => subset_ground h)).mp hJ).2
  exact Finset.mem_image.mp hK

#print axioms compressedStarPair_ground_eq_inter
#print axioms compressedStarPair_ground_eq_centers_union_present_isolates
#print axioms starPairTrueComplement_card
#print axioms starPairTrueComplement_rankTwo
#print axioms leafPairAvoidance_card_le_trueSupport_atoms
#print axioms original_member_of_starPairTrueComplement
end FranklForcingFiber
