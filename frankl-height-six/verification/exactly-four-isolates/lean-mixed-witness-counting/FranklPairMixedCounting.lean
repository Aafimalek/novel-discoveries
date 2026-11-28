import FranklBlockWitnesses
import FranklPairMixedDistinct

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- Count arbitrary verified mixed omissions, in addition to every standard
source-witness top and block maximum. The finite input is a set of
(source, nonempty isolate hole) pairs; all distinct inputs contribute. -/
theorem leaf_pair_count_with_blocks_and_mixed {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (K : Finset (α × Finset α))
    (hK : ∀ z ∈ K, z.1 ∈ sources G ∧ z.1 ≠ p ∧ z.1 ≠ q ∧
      z.2 ⊆ isolated G ∧ z.2.Nonempty ∧ mixedStarOmission G z.1 z.2 ∈ G) :
    (ground G).card + (sources G).card + (FranklBlockIncidence.away (starBlocks G) p q).card + K.card ≤
      (avoidBoth G (starLeaf G p) (starLeaf G q)).card + 1 := by
  classical
  let s := starLeaf G p
  let t := starLeaf G q
  let X := (sources G).image (sourceWitnessTop G hG hmin)
  let Y := (starPairMaxima G).filter (fun T => s ∈ T ∧ t ∈ T)
  let R := X ∪ Y
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  have hsep := weakMinimalGround_separated hG hmin
  obtain ⟨hs,ht,hts,_,hsT,htT⟩ := cross_pair_terminal_data hG hmin
    (mem_sources.mp hp).1 (mem_sources.mp hq).1 hpq hps hqt hFp hFq
  have hsL : s ∈ leaves G := mem_leaves.mpr ⟨hs,p,(mem_sources.mp hp).1,hps,hFp⟩
  have htL : t ∈ leaves G := mem_leaves.mpr ⟨ht,q,(mem_sources.mp hq).1,hqt,hFq⟩
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro A hX hY
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hX
    obtain ⟨b,hb,c,hc,hbc,he'⟩ := mem_starPairMaxima.mp (Finset.mem_filter.mp hY).1
    obtain ⟨hbs,hFb⟩ := starLeaf_spec hb
    have hbL : starLeaf G b ∈ leaves G := mem_leaves.mpr
      ⟨mem_ground_of_forces (mem_sources.mp hb).1 hFb,b,(mem_sources.mp hb).1,hbs,hFb⟩
    have hbA : starLeaf G b ∈ A := he ▸ (sourceWitnessTop_spec hG hmin ha).2.2.2.1 hbL
    exact starPairMax_omit_left G b c (he'.symm ▸ hbA)
  have hXcard : X.card = (sources G).card :=
    Finset.card_image_of_injOn (sourceWitnessTop_injOn hG hmin)
  have heY : Y.image (omittedStars G) = FranklBlockIncidence.away (starBlocks G) p q := by
    ext A
    constructor
    · intro hA
      obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨hTex,hIn⟩ := Finset.mem_filter.mp hT
      exact FranklBlockIncidence.mem_away.mpr ⟨Finset.mem_image.mpr ⟨T,hTex,rfl⟩,
        (fun h => (mem_omittedStars.mp h).2 hIn.1),(fun h => (mem_omittedStars.mp h).2 hIn.2)⟩
    · intro hA
      obtain ⟨hB,hpB,hqB⟩ := FranklBlockIncidence.mem_away.mp hA
      obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hB
      have hsT' : s ∈ T := by
        by_contra hn
        exact hpB (mem_omittedStars.mpr ⟨hp,hn⟩)
      have htT' : t ∈ T := by
        by_contra hn
        exact hqB (mem_omittedStars.mpr ⟨hq,hn⟩)
      exact Finset.mem_image.mpr ⟨T,Finset.mem_filter.mpr ⟨hT,hsT',htT'⟩,rfl⟩
  have hYcard : Y.card = (FranklBlockIncidence.away (starBlocks G) p q).card := by
    rw [← heY]
    symm
    exact Finset.card_image_of_injOn (fun A hA B hB he =>
      omittedStars_injOn_pairMaxima hG hmin (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1 he)
  have hR : ∀ ⦃A⦄, A ∈ R → A ∈ G ∧ s ∈ A ∧ t ∈ A ∧
      A ≠ ground G ∧ ∀ v ∈ ground G, A ≠ avoid G v := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨hT,haT,_,hLT,_⟩ := sourceWitnessTop_spec hG hmin ha
      refine ⟨hT,hLT hsL,hLT htL,?_,fun v hv => sourceWitnessTop_ne_avoid hG hmin ha hv⟩
      intro e
      exact haT (show a ∈ sourceWitnessTop G hG hmin a from e.symm ▸ (mem_sources.mp ha).1)
    · obtain ⟨hA,hIn⟩ := Finset.mem_filter.mp hA
      obtain ⟨a,ha,b,hb,hab,rfl⟩ := mem_starPairMaxima.mp hA
      obtain ⟨has,hFa⟩ := starLeaf_spec ha
      obtain ⟨hbt,hFb⟩ := starLeaf_spec hb
      have habs : ({a,b} : Finset α) ⊆ sources G := by
        intro z hz
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz
        exact hz.elim (fun e => e.symm ▸ ha) (fun e => e.symm ▸ hb)
      have hs' : starPairMax G a b ⊆ outsideStars G {a,b} := by
        intro z hz
        obtain ⟨hzG,_,_,hFaz,hFbz⟩ := cross_pair_top_mem_outside_of_mem hG hmin (mem_sources.mp ha).1
          (mem_sources.mp hb).1 hab has hbt hFa hFb hz
        apply mem_outsideStars.mpr
        refine ⟨hzG,?_⟩
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        exact hv.elim (fun e => e.symm ▸ hFaz) (fun e => e.symm ▸ hFbz)
      have hd : ground G \ outsideStars G {a,b} ⊆ ground G \ starPairMax G a b := by
        intro z hz
        obtain ⟨hzG,hn⟩ := Finset.mem_sdiff.mp hz
        exact Finset.mem_sdiff.mpr ⟨hzG,fun h => hn (hs' h)⟩
      have hMore : 2 < (ground G \ starPairMax G a b).card :=
        lt_of_lt_of_le (outsideStars_omit_more_than_two hG hmin habs (by simp) (by simp) hab)
          (Finset.card_le_card hd)
      refine ⟨starPairMax_mem_family hG hmin ha hb hab,hIn.1,hIn.2,?_,?_⟩
      · intro he
        rw [he,Finset.sdiff_self,Finset.card_empty] at hMore
        omega
      · intro v _ he
        rw [he] at hMore
        exact (Nat.not_lt_of_ge (card_omitted_single_avoid_le_two hG hmin v)) hMore
  let f : α × Finset α → Finset α := fun z => mixedStarOmission G z.1 z.2
  let M := K.image f
  have hf : Set.InjOn f (↑K : Set (α × Finset α)) := by
    intro a ha b hb he
    obtain ⟨haS,_,_,haI,_,_⟩ := hK a ha
    obtain ⟨hbS,_,_,hbI,_,_⟩ := hK b hb
    change mixedStarOmission G a.1 a.2 = mixedStarOmission G b.1 b.2 at he
    have hab : a.1 = b.1 := by
      by_contra hn
      exact mixedStarOmission_ne_of_sources_ne hG hmin haS hbS hn hbI he
    apply Prod.ext hab
    exact mixedStarOmission_hole_injective haS haI hbI (hab.symm ▸ he)
  have hMcard : M.card = K.card := Finset.card_image_of_injOn hf
  have hRM : Disjoint R M := Finset.disjoint_left.mpr (by
    intro A hA hM
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨hr,_,_,hI,_,_⟩ := hK z hz
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hA
      exact mixedStarOmission_ne_sourceWitnessTop hG hmin hr hv z.2 he.symm
    · exact mixedStarOmission_notMem_pairMaxima hG hmin hr hI (Finset.mem_filter.mp hA).1)
  have hAll : ∀ ⦃A⦄, A ∈ R ∪ M → A ∈ G ∧ s ∈ A ∧ t ∈ A ∧
      A ≠ ground G ∧ ∀ v ∈ ground G, A ≠ avoid G v := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact hR hA
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨hr,hrp,hrq,hI,hn,hzG⟩ := hK z hz
      exact ⟨hzG, chosen_leaf_mem_mixedOther hG hmin hr hp hrp hI,
        chosen_leaf_mem_mixedOther hG hmin hr hq hrq hI,
        mixedStarOmission_ne_ground hr z.2, fun _ _ => mixedStarOmission_ne_avoid hr hI hn⟩
  have hlo := terminal_pair_avoidance_extra_noncanonical hG hsep hs ht hts hsT htT hAll
  have hRc : R.card = X.card + Y.card := Finset.card_union_of_disjoint hXY
  rw [Finset.card_union_of_disjoint hRM,hRc,hXcard,hYcard,hMcard] at hlo
  omega

#print axioms leaf_pair_count_with_blocks_and_mixed
end FranklForcingFiber
