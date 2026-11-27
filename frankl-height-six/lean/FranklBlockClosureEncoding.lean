import FranklExcludeElevenStars

namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- Outside pairs whose unique block meets the fixed block. -/
noncomputable def blockLinks (S : Finset α) (B : Finset (Finset α)) (A : Finset α) :
    Finset (Finset α) := by
  classical
  exact (S \ A).powersetCard 2 |>.filter (fun e =>
    ∃ T ∈ B, e ⊆ T ∧ (A ∩ T).Nonempty)

theorem mem_blockLinks {S : Finset α} {B : Finset (Finset α)} {A e : Finset α} :
    e ∈ blockLinks S B A ↔ e ⊆ S \ A ∧ e.card = 2 ∧
      ∃ T ∈ B, e ⊆ T ∧ (A ∩ T).Nonempty := by
  classical
  unfold blockLinks
  rw [Finset.mem_filter,Finset.mem_powersetCard,and_assoc]

end FranklBlockIncidence

namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

theorem pair_representatives_of_block {G : Finset (Finset α)} {A : Finset α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hAB : A ∈ starBlocks G) :
    ∃ p ∈ sources G, ∃ q ∈ sources G, p ≠ q ∧ p ∈ A ∧ q ∈ A ∧
      A = omittedStars G (starPairMax G p q) := by
  obtain ⟨hsub,h2⟩ := (starBlocks_pairDesign hG hmin).1 A hAB
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  have hpG := hsub hp
  have hqG := hsub hq
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hAB
  exact ⟨p,hpG,q,hqG,hpq,hp,hq,congrArg (omittedStars G)
    (starPairMax_eq_of_omits_pair hG hmin hT hp hq hpq)⟩

theorem compressed_pair_subset_outside_block_or_isolates {G : Finset (Finset α)}
    {A Z : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hEq : A = omittedStars G (starPairMax G p q))
    (hZ : Z ∈ compressPair G p q (starLeaf G p) (starLeaf G q)) :
    Z ⊆ (sources G \ A) ∪ isolated G := by
  intro z hz
  have hzR := mem_pairReps.mp (compressPair_subset_reps hZ hz)
  by_cases hzS : z ∈ sources G
  · have hzT : z ∈ starPairMax G p q :=
      mem_raw_ground_of_mem_compress_ground (subset_ground hZ hz)
    have hnA : z ∉ A := by
      intro h
      rw [hEq] at h
      exact (mem_omittedStars.mp h).2
        ((starLeaf_spec hzS).2 (starPairMax_mem_family hG hmin hp hq hpq) hzT)
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hzS,hnA⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hzR.1,hzR.2.1⟩,hzS⟩))

/-- Every pair linked through the fixed omitted block has the same
occurrence signature on the compressed avoidance fiber. -/
theorem compressed_pair_signatures_eq_of_blockLink {G : Finset (Finset α)}
    {A e : Finset α} {p q u v : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) (hpA : p ∈ A) (hqA : q ∈ A)
    (hEq : A = omittedStars G (starPairMax G p q))
    (he : e ∈ blockLinks (sources G) (starBlocks G) A) (hu : u ∈ e) (hv : v ∈ e) :
    let K := compressPair G p q (starLeaf G p) (starLeaf G q)
    signature K u = signature K v := by
  obtain ⟨hESub,_,T,hT,heT,hTb⟩ := mem_blockLinks.mp he
  obtain ⟨b,hb⟩ := hTb
  obtain ⟨huS,huA⟩ := Finset.mem_sdiff.mp (hESub hu)
  obtain ⟨hvS,hvA⟩ := Finset.mem_sdiff.mp (hESub hv)
  obtain ⟨hbA,hbT⟩ := Finset.mem_inter.mp hb
  have hbOm : b ∈ omittedStars G (starPairMax G p q) := hEq ▸ hbA
  have hpu : p ≠ u := fun e' => huA (e' ▸ hpA)
  have hqu : q ≠ u := fun e' => huA (e' ▸ hqA)
  have hpv : p ≠ v := fun e' => hvA (e' ▸ hpA)
  have hqv : q ≠ v := fun e' => hvA (e' ▸ hqA)
  have hbu : b ≠ u := fun e' => huA (e' ▸ hbA)
  have hbv : b ≠ v := fun e' => hvA (e' ▸ hbA)
  have huR : u ∈ pairReps G p q := mem_pairReps.mpr ⟨(mem_sources.mp huS).1,
    (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin huS)).2,hpu.symm,hqu.symm⟩
  have hvR : v ∈ pairReps G p q := mem_pairReps.mpr ⟨(mem_sources.mp hvS).1,
    (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin hvS)).2,hpv.symm,hqv.symm⟩
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  let K := compressPair G p q (starLeaf G p) (starLeaf G q)
  have hmem {Z : Finset α} (hZ : Z ∈ K) : u ∈ Z ↔ v ∈ Z := by
    obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hZ
    obtain ⟨hXG,hXn⟩ := Finset.mem_filter.mp hX
    obtain ⟨hus,hFu⟩ := starLeaf_spec huS
    obtain ⟨hvs,hFv⟩ := starLeaf_spec hvS
    have h1 := local_twins_across_stars hG hmin (mem_sources.mp hp).1 (mem_sources.mp huS).1
      hps hus hpu hFp hFu hXG (fun h => hXn (Or.inl h))
    have h2 := local_twins_across_stars hG hmin (mem_sources.mp hp).1 (mem_sources.mp hvS).1
      hps hvs hpv hFp hFv hXG (fun h => hXn (Or.inl h))
    have hL := leaf_membership_iff_of_link_block hG hmin hp hq hpq hX hbOm
      hT hbT (heT hu) (heT hv) hbu hbv
    have hvu := h1.trans (hL.trans h2.symm)
    change u ∈ X ∩ pairReps G p q ↔ v ∈ X ∩ pairReps G p q
    simp only [Finset.mem_inter,huR,hvR,and_true]
    exact hvu
  ext Z
  change (Z ∈ K.filter (u ∈ ·)) ↔ (Z ∈ K.filter (v ∈ ·))
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1,(hmem h.1).mp h.2⟩,fun h => ⟨h.1,(hmem h.1).mpr h.2⟩⟩

theorem pair_fiber_card_le_pow_block_signatures {G : Finset (Finset α)}
    {A : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hEq : A = omittedStars G (starPairMax G p q)) :
    let K := compressPair G p q (starLeaf G p) (starLeaf G q)
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤
      2 ^ ((((sources G) \ A).image (signature K)).card + (isolated G).card) := by
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  have he := cross_pair_compress_card hG hmin (mem_sources.mp hp).1 (mem_sources.mp hq).1 hpq hps hqt hFp hFq
  rw [← he]
  exact family_card_le_pow_signatures (fun _ hZ =>
    compressed_pair_subset_outside_block_or_isolates hG hmin hp hq hpq hEq hZ)

/-- Eight outsiders and seven links leave only four distinct signatures. -/
theorem pair_fiber_le_thirtytwo_of_eight_seven {G : Finset (Finset α)}
    {A : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) (hpA : p ∈ A) (hqA : q ∈ A)
    (hEq : A = omittedStars G (starPairMax G p q))
    (h8 : (sources G \ A).card = 8) (h7 : 7 ≤ (blockLinks (sources G) (starBlocks G) A).card) :
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 32 := by
  let E := sources G \ A
  let K := compressPair G p q (starLeaf G p) (starLeaf G q)
  let f := signature K
  have hlabels : (E.image f).card ≤ 4 := by
    by_contra! hbad
    have h6 := equal_label_pairs_card_le_six f h8 (show 5 ≤ (E.image f).card by omega)
    have hsub : blockLinks (sources G) (starBlocks G) A ⊆ (E.image f).biUnion
        (fun y => (E.filter (fun z => f z = y)).powersetCard 2) := by
      intro D hD
      obtain ⟨hEs,hD2,_⟩ := mem_blockLinks.mp hD
      obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < D.card by omega)
      exact Finset.mem_biUnion.mpr ⟨f u,Finset.mem_image_of_mem f (hEs hu),
        Finset.mem_powersetCard.mpr ⟨fun v hv => Finset.mem_filter.mpr ⟨hEs hv,
          compressed_pair_signatures_eq_of_blockLink hG hmin hp hq hpq hpA hqA hEq hD hv hu⟩,hD2⟩⟩
    have he := Finset.card_le_card hsub
    exact (Nat.not_lt_of_ge (he.trans h6)) h7
  have h := pair_fiber_card_le_pow_block_signatures hG hmin hp hq hpq hEq
  have hd : (E.image f).card + (isolated G).card ≤ 5 := by omega
  exact h.trans (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hd)

#print axioms compressed_pair_signatures_eq_of_blockLink
#print axioms pair_fiber_card_le_pow_block_signatures
#print axioms pair_fiber_le_thirtytwo_of_eight_seven
end FranklForcingFiber
