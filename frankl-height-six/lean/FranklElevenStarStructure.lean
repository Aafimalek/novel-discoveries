import FranklBlockWitnesses

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- The omitted stars of any member are closed under the blocks through
their pairs. -/
theorem omittedStars_block_closed {G : Finset (Finset α)} {A : Finset α} {p q : α}
    (hA : A ∈ G) (hp : p ∈ omittedStars G A) (hq : q ∈ omittedStars G A)
    (_hpq : p ≠ q) :
    omittedStars G (starPairMax G p q) ⊆ omittedStars G A := by
  have hn := (mem_omittedStars.mp hp).2
  have hm := (mem_omittedStars.mp hq).2
  have hsub : A ⊆ starPairMax G p q := subset_ground
    (show A ∈ avoidBoth G (starLeaf G p) (starLeaf G q) from
      Finset.mem_filter.mpr ⟨hA,fun h => h.elim hn hm⟩)
  intro v hv
  obtain ⟨hvS,hvN⟩ := mem_omittedStars.mp hv
  exact mem_omittedStars.mpr ⟨hvS,fun h => hvN (hsub h)⟩

/-- A link block through a star omitted by the chosen pair identifies the
two other linked leaf coordinates on every member of that pair fiber. -/
theorem leaf_membership_iff_of_link_block {G : Finset (Finset α)} {A B : Finset α}
    {p q b u v : α} (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hA : A ∈ avoidBoth G (starLeaf G p) (starLeaf G q))
    (hb : b ∈ omittedStars G (starPairMax G p q))
    (hB : B ∈ starBlocks G) (hbB : b ∈ B) (huB : u ∈ B) (hvB : v ∈ B)
    (hbu : b ≠ u) (hbv : b ≠ v) :
    starLeaf G u ∈ A ↔ starLeaf G v ∈ A := by
  classical
  obtain ⟨hAG,hAn⟩ := Finset.mem_filter.mp hA
  have hpA := mem_omittedStars.mpr ⟨hp,fun h => hAn (Or.inl h)⟩
  have hqA := mem_omittedStars.mpr ⟨hq,fun h => hAn (Or.inr h)⟩
  have hbA := omittedStars_block_closed hAG hpA hqA hpq hb
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hB
  have haux {x y : α} (hx : x ∈ omittedStars G T) (hy : y ∈ omittedStars G T)
      (hbx : b ≠ x) (hxA : starLeaf G x ∉ A) : starLeaf G y ∉ A := by
    have he := starPairMax_eq_of_omits_pair hG hmin hT hbB hx hbx
    have hxA' := mem_omittedStars.mpr ⟨(mem_omittedStars.mp hx).1,hxA⟩
    have h := omittedStars_block_closed hAG hbA hxA' hbx (he ▸ hy)
    exact (mem_omittedStars.mp h).2
  exact ⟨fun hu => by
    by_contra hn
    exact haux hvB huB hbv hn hu,
  fun hv => by
    by_contra hn
    exact haux huB hvB hbu hn hv⟩

/-- At eleven sources and one isolate, the incidence estimate rules out
blocks larger than triples. Every pair fiber has at least forty-two
members, and every compressed pair support has at least nine points. -/
theorem one_isolate_eleven_star_structure {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1) (hk : (sources G).card = 11) :
    (∀ A ∈ starBlocks G, A.card ≤ 3) ∧
    ∀ p ∈ sources G, ∀ q ∈ sources G, p ≠ q →
      42 ≤ (avoidBoth G (starLeaf G p) (starLeaf G q)).card ∧
      9 ≤ (ground (compressPair G p q (starLeaf G p) (starLeaf G q))).card := by
  have hD := starBlocks_pairDesign hG hmin
  have hPart := partition_card hG hmin
  have hLeaves := sources_card_le_leaves hG hmin
  have hn : 23 ≤ (ground G).card := by omega
  have hLower {p q : α} (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
      33 + (FranklBlockIncidence.away (starBlocks G) p q).card ≤
        (avoidBoth G (starLeaf G p) (starLeaf G q)).card := by
    have h := leaf_pair_count_with_blocks hG hmin hp hq hpq
    omega
  have hr4 : ∀ A ∈ starBlocks G, A.card ≤ 4 := by
    intro A hA
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨a,ha,b,hb,hab,rfl⟩ := mem_starPairMaxima.mp hT
    by_contra! hn'
    have hu := cross_pair_actual_upper_of_omitted hG hmin ha hb hab
    dsimp only at hu
    rw [hI,hk] at hu
    have hcap : 1 + (11 - (omittedStars G (starPairMax G a b)).card) ≤ 7 := by omega
    have hc := Nat.choose_le_choose 2 hcap
    have hc' : Nat.choose 7 2 = 21 := by decide
    have hLo := hLower ha hb hab
    omega
  have h5 {p q : α} (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
      5 ≤ (FranklBlockIncidence.away (starBlocks G) p q).card := by
    have hgap : (4-1)*(2-1)+2*(4-2) < (sources G).card-3 := by rw [hk]; decide
    have h := FranklBlockIncidence.away_card_mul_lower hD hp hq hpq (r := 4) (d := 2) hr4 hgap
    rw [hk] at h
    omega
  have hr3 : ∀ A ∈ starBlocks G, A.card ≤ 3 := by
    intro A hA
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨a,ha,b,hb,hab,rfl⟩ := mem_starPairMaxima.mp hT
    by_contra! hn'
    have hu := cross_pair_actual_upper_of_omitted hG hmin ha hb hab
    dsimp only at hu
    rw [hI,hk] at hu
    have hcap : 1 + (11 - (omittedStars G (starPairMax G a b)).card) ≤ 8 := by omega
    have hc := Nat.choose_le_choose 2 hcap
    have hc' : Nat.choose 8 2 = 28 := by decide
    have hLo := hLower ha hb hab
    have hW := h5 ha hb hab
    omega
  refine ⟨hr3,?_⟩
  intro p hp q hq hpq
  have hgap : (3-1)*(3-1)+2*(3-2) < (sources G).card-3 := by rw [hk]; decide
  have hW := FranklBlockIncidence.away_card_mul_lower hD hp hq hpq (r := 3) (d := 3) hr3 hgap
  rw [hk] at hW
  have hLo := hLower hp hq hpq
  have hf : 42 ≤ (avoidBoth G (starLeaf G p) (starLeaf G q)).card := by omega
  refine ⟨hf,?_⟩
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  have hpG := (mem_sources.mp hp).1
  have hqG := (mem_sources.mp hq).1
  let C := compressPair G p q (starLeaf G p) (starLeaf G q)
  have hC : C.card = (avoidBoth G (starLeaf G p) (starLeaf G q)).card :=
    cross_pair_compress_card hG hmin hpG hqG hpq hps hqt hFp hFq
  have h4 := cross_pair_compress_noFourChain hG hmin hpG hqG hpq hps hqt hFp hFq
    (cross_pair_noFourChain hG hmin hpG hqG hpq hps hqt hFp hFq)
  have hu := FranklHeightThreeSauer.card_le (ground C)
    (compress_pair_unionClosed hG.2.2.1) h4 (fun _ hA => subset_ground hA)
  change C.card ≤ 1+(ground C).card+(ground C).card.choose 2 at hu
  change 9 ≤ (ground C).card
  by_contra! hbad
  have hc := Nat.choose_le_choose 2 (show (ground C).card ≤ 8 by omega)
  have hc' : Nat.choose 8 2 = 28 := by decide
  omega

#print axioms omittedStars_block_closed
#print axioms leaf_membership_iff_of_link_block
#print axioms one_isolate_eleven_star_structure

end FranklForcingFiber
