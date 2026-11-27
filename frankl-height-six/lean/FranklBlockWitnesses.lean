import FranklOmittedStarBlocks
import FranklOneIsolateSmallSources

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- Both the source-witness maxima and the distinct pair maxima whose
omitted blocks avoid the selected sources give extra pair-avoidance counts. -/
theorem leaf_pair_count_with_blocks {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
    (ground G).card + (sources G).card + (FranklBlockIncidence.away (starBlocks G) p q).card ≤
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
  have hlo := terminal_pair_avoidance_extra_noncanonical hG hsep hs ht hts hsT htT hR
  have hRc : R.card = X.card + Y.card := Finset.card_union_of_disjoint hXY
  rw [hRc,hXcard,hYcard] at hlo
  change (ground G).card + (sources G).card + (FranklBlockIncidence.away (starBlocks G) p q).card ≤
    (avoidBoth G s t).card + 1
  exact (Nat.add_assoc _ _ _).symm ▸ hlo

/-- A unique isolate and a forcing edge need at least eleven sources. -/
theorem one_isolate_nonzero_sources_ge_eleven {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1) (hk : 0 < (sources G).card) : 11 ≤ (sources G).card := by
  by_contra! hBad
  let k := (sources G).card
  have hk9 : 9 ≤ k := one_isolate_nonzero_sources_ge_nine hG hmin hI hk
  have hk10 : k ≤ 10 := by omega
  have hN := partition_card hG hmin
  have hLeaves := sources_card_le_leaves hG hmin
  have hn : 2*k+1 ≤ (ground G).card := by omega
  let B := starBlocks G
  have hD := starBlocks_pairDesign hG hmin
  have hlo {a b : α} (ha : a ∈ sources G) (hb : b ∈ sources G) (hab : a ≠ b) :
      3*k + (FranklBlockIncidence.away B a b).card ≤
        (avoidBoth G (starLeaf G a) (starLeaf G b)).card := by
    have h := leaf_pair_count_with_blocks hG hmin ha hb hab
    change (ground G).card + k + (FranklBlockIncidence.away B a b).card ≤
      (avoidBoth G (starLeaf G a) (starLeaf G b)).card+1 at h
    omega
  have hr3 : ∀ A ∈ B, A.card ≤ 3 := by
    intro A hA
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨a,ha,b,hb,hab,rfl⟩ := mem_starPairMaxima.mp hT
    by_contra! hLarge
    have hu := cross_pair_actual_upper_of_omitted hG hmin ha hb hab
    dsimp only at hu
    rw [hI] at hu
    have hcap : 1 + (k - (omittedStars G (starPairMax G a b)).card) ≤ k - 3 := by omega
    change (avoidBoth G (starLeaf G a) (starLeaf G b)).card ≤
      1+(1+(k-(omittedStars G (starPairMax G a b)).card)) +
        (1+(k-(omittedStars G (starPairMax G a b)).card)).choose 2 at hu
    have hchoose := Nat.choose_le_choose 2 hcap
    have hnum : 1+(k-3)+(k-3).choose 2 < 3*k := by interval_cases k <;> decide
    have hl := hlo ha hb hab
    omega
  have hr2 : ∀ A ∈ B, A.card ≤ 2 := by
    intro A hA
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨a,ha,b,hb,hab,rfl⟩ := mem_starPairMaxima.mp hT
    by_contra! hLarge
    let W := (FranklBlockIncidence.away B a b).card
    have hW : 1+(k-2)+(k-2).choose 2 < 3*k+W := by
      by_cases hk' : k = 9
      · have hGap : (3-1)*(2-1)+2*(3-2) < (sources G).card-3 := by
          change (3-1)*(2-1)+2*(3-2) < k-3
          rw [hk']
          decide
        have hw := FranklBlockIncidence.away_card_mul_lower hD ha hb hab (r := 3) (d := 2) hr3 hGap
        change (k-2)*2 ≤ W*3 at hw
        rw [hk'] at hw ⊢
        change 14 ≤ W*3 at hw
        change 29 < 27+W
        omega
      · have hk' : k=10 := by omega
        have hGap : (3-1)*(3-1)+2*(3-2) < (sources G).card-3 := by
          change (3-1)*(3-1)+2*(3-2) < k-3
          rw [hk']
          decide
        have hw := FranklBlockIncidence.away_card_mul_lower hD ha hb hab (r := 3) (d := 3) hr3 hGap
        change (k-2)*3 ≤ W*3 at hw
        rw [hk'] at hw ⊢
        change 24 ≤ W*3 at hw
        change 37 < 30+W
        omega
    have hu := cross_pair_actual_upper_of_omitted hG hmin ha hb hab
    dsimp only at hu
    rw [hI] at hu
    have hcap : 1 + (k - (omittedStars G (starPairMax G a b)).card) ≤ k - 2 := by omega
    have hchoose := Nat.choose_le_choose 2 hcap
    have hl := hlo ha hb hab
    change 3*k+W ≤ _ at hl
    change (avoidBoth G (starLeaf G a) (starLeaf G b)).card ≤
      1+(1+(k-(omittedStars G (starPairMax G a b)).card)) +
        (1+(k-(omittedStars G (starPairMax G a b)).card)).choose 2 at hu
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < (sources G).card by omega)
  let W := (FranklBlockIncidence.away B a b).card
  let N := (avoidBoth G (starLeaf G a) (starLeaf G b)).card
  have hl : 3*k+W ≤ N := hlo ha hb hab
  obtain ⟨has,hFa⟩ := starLeaf_spec ha
  obtain ⟨hbt,hFb⟩ := starLeaf_spec hb
  have hu := cross_pair_avoidance_upper hG hmin (mem_sources.mp ha).1 (mem_sources.mp hb).1 hab has hbt hFa hFb
  rw [pairReps_card_formula hG hmin ha hb hab,hI] at hu
  have hrep : 1+(sources G).card-2 = k-1 := by omega
  rw [hrep] at hu
  change N ≤ 1+(k-1)+(k-1).choose 2 at hu
  by_cases hk' : k = 9
  · have hGap : (2-1)*(6-1)+2*(2-2) < (sources G).card-3 := by
      change (2-1)*(6-1)+2*(2-2) < k-3
      rw [hk']
      decide
    have hw := FranklBlockIncidence.away_card_mul_lower hD ha hb hab (r := 2) (d := 6) hr2 hGap
    change (k-2)*6 ≤ W*2 at hw
    rw [hk'] at hw hl hu
    change 42 ≤ W*2 at hw
    change 27+W ≤ N at hl
    change N ≤ 37 at hu
    omega
  · have hk' : k=10 := by omega
    have hGap : (2-1)*(7-1)+2*(2-2) < (sources G).card-3 := by
      change (2-1)*(7-1)+2*(2-2) < k-3
      rw [hk']
      decide
    have hw := FranklBlockIncidence.away_card_mul_lower hD ha hb hab (r := 2) (d := 7) hr2 hGap
    change (k-2)*7 ≤ W*2 at hw
    rw [hk'] at hw hl hu
    change 56 ≤ W*2 at hw
    change 30+W ≤ N at hl
    change N ≤ 46 at hu
    omega

#print axioms leaf_pair_count_with_blocks
#print axioms one_isolate_nonzero_sources_ge_eleven

end FranklForcingFiber
