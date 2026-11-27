import FranklNineOutsiderGroups
import FranklDenseSignatureCounts
import FranklThirteenDegreeMoment

namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

theorem block_eq_omitted_for_member_pair {G : Finset (Finset α)} {A : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hA : A ∈ starBlocks G) (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q) :
    A = omittedStars G (starPairMax G p q) := by
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hA
  exact congrArg (omittedStars G) (starPairMax_eq_of_omits_pair hG hmin hT hp hq hpq)

/-- The published one-isolate block argument excludes thirteen sources. -/
theorem one_isolate_excludes_thirteen_sources {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1) (hk : (sources G).card = 13) : False := by
  classical
  let B := starBlocks G
  have hD : PairDesign (sources G) B := starBlocks_pairDesign hG hmin
  have hPart := partition_card hG hmin
  have hLeaves := sources_card_le_leaves hG hmin
  have hn : 27 ≤ (ground G).card := by omega
  have hlo {p q : α} (hp : p ∈ sources G) (hq : q ∈ sources G) (hne : p ≠ q) :
      39 + (away B p q).card ≤ (avoidBoth G (starLeaf G p) (starLeaf G q)).card := by
    have h := leaf_pair_count_with_blocks hG hmin hp hq hne
    change (ground G).card + (sources G).card + (away B p q).card ≤ _ at h
    omega
  have hr5 : ∀ A ∈ B, A.card ≤ 5 := by
    intro A hA
    obtain ⟨p,hp,q,hq,hne,_,_,hEq⟩ := pair_representatives_of_block hG hmin hA
    by_contra! hd
    have hhi := cross_pair_actual_upper_of_omitted hG hmin hp hq hne
    dsimp only at hhi
    rw [← hEq,hI,hk] at hhi
    have hc : 1+(13-A.card)≤8 := by omega
    have hChoose := Nat.choose_le_choose 2 hc
    have h8 : Nat.choose 8 2 = 28 := by decide
    have hlow := hlo hp hq hne
    omega
  have hr4 : ∀ A ∈ B, A.card ≤ 4 := by
    intro A hA
    by_contra! hd
    have hA5 : A.card = 5 := by have h := hr5 A hA; omega
    obtain ⟨p,hp,q,hq,hne,hpA,hqA,hEq⟩ := pair_representatives_of_block hG hmin hA
    have he := Finset.card_sdiff_add_card_eq_card (hD.1 A hA).1
    have h8 : (sources G \ A).card = 8 := by omega
    have hl := hlo hp hq hne
    by_cases hL : 7 ≤ (blockLinks (sources G) B A).card
    · have h32 := pair_fiber_le_thirtytwo_of_eight_seven hG hmin hI hp hq hne hpA hqA hEq h8 hL
      omega
    · have hAp := Finset.card_erase_add_one hpA
      have hAqmem : q ∈ A.erase p := Finset.mem_erase.mpr ⟨hne.symm,hqA⟩
      have hAq := Finset.card_erase_add_one hAqmem
      obtain ⟨b,hb,c,hc,hbc⟩ := Finset.one_lt_card.mp (show 1 < ((A.erase p).erase q).card by omega)
      obtain ⟨hbq,hb'⟩ := Finset.mem_erase.mp hb
      obtain ⟨hbp,hbA⟩ := Finset.mem_erase.mp hb'
      obtain ⟨hcq,hc'⟩ := Finset.mem_erase.mp hc
      obtain ⟨hcp,hcA⟩ := Finset.mem_erase.mp hc'
      have hW := away_card_ge_eleven_of_four_block_eight_six hD hA hpA hqA hbA hcA
        hbp hbq hcp hcq hbc h8 (by omega)
      have hhi := cross_pair_actual_upper_of_omitted hG hmin hp hq hne
      dsimp only at hhi
      rw [← hEq,hI,hk,hA5] at hhi
      change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 46 at hhi
      omega
  have hr3 : ∀ A ∈ B, A.card ≤ 3 := by
    intro A hA
    by_contra! hd
    have hA4 : A.card = 4 := by have h := hr4 A hA; omega
    have he := Finset.card_sdiff_add_card_eq_card (hD.1 A hA).1
    have h9 : (sources G \ A).card = 9 := by omega
    by_cases hL : 11 ≤ (blockLinks (sources G) B A).card
    · obtain ⟨p,hp,q,hq,hne,hpA,hqA,hEq⟩ := pair_representatives_of_block hG hmin hA
      have h32 := pair_fiber_le_thirtytwo_of_nine_eleven hG hmin hI hp hq hne hpA hqA hEq h9 hL
      have hl := hlo hp hq hne
      omega
    · obtain ⟨p,hpA,q,hqA,hne,hW⟩ :=
        some_away_card_ge_eighteen_of_four_block_nine_ten hD hr4 hA hA4 h9 (by omega)
      have hp := (hD.1 A hA).1 hpA
      have hq := (hD.1 A hA).1 hqA
      have hEq := block_eq_omitted_for_member_pair hG hmin hA hpA hqA hne
      have hl := hlo hp hq hne
      have hhi := cross_pair_actual_upper_of_omitted hG hmin hp hq hne
      dsimp only at hhi
      rw [← hEq,hI,hk,hA4] at hhi
      change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 56 at hhi
      omega
  have hW {p q : α} (hp : p ∈ sources G) (hq : q ∈ sources G) (hne : p ≠ q) :
      (away B p q).card + 2*(triples B).card =
        55 + tripleDegree B p + tripleDegree B q := by
    have h := away_card_exact_of_triples hD hr3 hp hq hne
    rw [hk] at h
    have hchoose : Nat.choose 13 2 = 78 := by decide
    omega
  have hT : (triples B).Nonempty := by
    by_contra hne
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (show 1 < (sources G).card by omega)
    obtain ⟨hps,hFp⟩ := starLeaf_spec hp
    obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
    have w := hW hp hq hpq
    simp [tripleDegree,hempty] at w
    have hl := hlo hp hq hpq
    have hu := cross_pair_avoidance_upper hG hmin (mem_sources.mp hp).1 (mem_sources.mp hq).1
      hpq hps hqt hFp hFq
    rw [pairReps_card_formula hG hmin hp hq hpq,hI,hk] at hu
    change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 79 at hu
    omega
  have hCap : ∀ A ∈ triples B, ∀ p ∈ A, ∀ q ∈ A, p ≠ q →
      tripleDegree B p + tripleDegree B q + 27 ≤ 2*(triples B).card := by
    intro A hA p hpA q hqA hne
    obtain ⟨hAB,hA3⟩ := Finset.mem_filter.mp hA
    have hp := (hD.1 A hAB).1 hpA
    have hq := (hD.1 A hAB).1 hqA
    have hEq := block_eq_omitted_for_member_pair hG hmin hAB hpA hqA hne
    have hu := cross_pair_actual_upper_of_omitted hG hmin hp hq hne
    dsimp only at hu
    rw [← hEq, hA3, hI, hk] at hu
    change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 67 at hu
    have h := hW hp hq hne
    have hl := hlo hp hq hne
    omega
  obtain ⟨A,hA,hDeg⟩ := exists_high_triple_degree_sum_thirteen hD hr3 hk hT hCap
  have hA3 := (Finset.mem_filter.mp hA).2
  have hDegEq := match_triple_degree_sum_to_links hD hA
  have hLinkEq := linkEdges_card_eq_linkTriples hD hA
  have hLink10 : 10 ≤ (linkEdges B A).card := by omega
  obtain ⟨p,hp,q,hq,hpq,hpA,hqA,hEq⟩ := pair_representatives_of_triple hG hmin hA
  let E := sources G \ A
  let K := compressPair G p q (starLeaf G p) (starLeaf G q)
  let f := signature K
  let P := blockLinks (sources G) B A
  have hES : E.card = 10 := by
    have hh := Finset.card_sdiff_add_card_eq_card (hD.1 A (Finset.mem_filter.mp hA).1).1
    change E.card + A.card = (sources G).card at hh
    omega
  have hsub : linkEdges B A ⊆ P := by
    intro e he
    obtain ⟨heS,he2,T,hT,v,hV,heT⟩ := link_edge_data hD hA he
    exact mem_blockLinks.mpr ⟨heS,he2,T,(Finset.mem_filter.mp hT).1,heT,⟨v,hV⟩⟩
  have hP10 := hLink10.trans (Finset.card_le_card hsub)
  have hSame : ∀ e ∈ P, e ⊆ E ∧ e.card = 2 ∧ ∀ u ∈ e, ∀ v ∈ e, f u = f v := by
    intro e he
    obtain ⟨hsub,h2,_⟩ := mem_blockLinks.mp he
    exact ⟨hsub,h2,fun u hu v hv =>
      compressed_pair_signatures_eq_of_blockLink hG hmin hp hq hpq hpA hqA hEq he hu hv⟩
  have hlabels := image_card_le_four_of_ten_matchings f hES hP10 hSame
    (card_links_in_subset_le_three_half hD hr3 hA3)
  have hcap := pair_fiber_card_le_pow_block_signatures hG hmin hp hq hpq hEq
  have h5 : (E.image f).card + (isolated G).card ≤ 5 := by omega
  have h32 : (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 32 :=
    hcap.trans (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) h5)
  have hLow := hlo hp hq hpq
  omega

/-- Exactly one isolated point and nonzero forcing require at least fourteen sources. -/
theorem one_isolate_nonzero_sources_ge_fourteen {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1) (hk : 0 < (sources G).card) :
    14 ≤ (sources G).card := by
  have hlo := one_isolate_nonzero_sources_ge_thirteen hG hmin hI hk
  by_contra! hcap
  exact one_isolate_excludes_thirteen_sources hG hmin hI (by omega)

#print axioms one_isolate_excludes_thirteen_sources
#print axioms one_isolate_nonzero_sources_ge_fourteen
end FranklForcingFiber
