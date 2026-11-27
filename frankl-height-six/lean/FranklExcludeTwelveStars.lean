import FranklNineSignatureMatching

open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

theorem exists_high_triple_degree_sum_twelve {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B) (h3 : ∀ A ∈ B, A.card ≤ 3)
    (hk : S.card = 12) (ht : 14 ≤ (triples B).card) :
    ∃ A ∈ triples B, 11 ≤ ∑ v ∈ A, tripleDegree B v := by
  classical
  by_contra hn
  have hdv : ∀ v ∈ S, tripleDegree B v ≤ 5 := by
    intro v hv
    have h := card_containing_add_tripleDegree hD h3 hv
    have hsub : (triples B).filter (v ∈ ·) ⊆ B.filter (v ∈ ·) :=
      fun A hA => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1,
        (Finset.mem_filter.mp hA).2⟩
    have hc := Finset.card_le_card hsub
    change tripleDegree B v ≤ _ at hc
    omega
  have hnum (d : ℕ) (hd : d ≤ 5) : 7*d ≤ d^2 + 12 := by interval_cases d <;> decide
  have h := Finset.sum_le_sum (s := S) (fun v hv => hnum (tripleDegree B v) (hdv v hv))
  rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hk,sum_tripleDegree hD] at h
  have h' : (∑ A ∈ triples B, ∑ v ∈ A, tripleDegree B v) ≤ ∑ _A ∈ triples B, 10 := by
    apply Finset.sum_le_sum
    intro A hA
    by_contra! ha
    exact hn ⟨A,hA,by omega⟩
  rw [← sum_sq_tripleDegree hD,Finset.sum_const,nsmul_eq_mul] at h'
  change (∑ v ∈ S, (tripleDegree B v)^2) ≤ (triples B).card * 10 at h'
  omega

end FranklBlockIncidence

namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- The published one-isolate block argument excludes twelve sources. -/
theorem one_isolate_excludes_twelve_sources {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1) (hk : (sources G).card = 12) : False := by
  classical
  let B := starBlocks G
  have hD : PairDesign (sources G) B := starBlocks_pairDesign hG hmin
  have hPart := partition_card hG hmin
  have hLeaves := sources_card_le_leaves hG hmin
  have hn : 25 ≤ (ground G).card := by omega
  have hlo {p q : α} (hp : p ∈ sources G) (hq : q ∈ sources G) (hne : p ≠ q) :
      36 + (away B p q).card ≤ (avoidBoth G (starLeaf G p) (starLeaf G q)).card := by
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
    have hc : 1+(12-A.card)≤7 := by omega
    have hChoose := Nat.choose_le_choose 2 hc
    have h7 : Nat.choose 7 2 = 21 := by decide
    have hlow := hlo hp hq hne
    omega
  have hr4 : ∀ A ∈ B, A.card ≤ 4 := by
    intro A hA
    obtain ⟨p,hp,q,hq,hne,_,_,hEq⟩ := pair_representatives_of_block hG hmin hA
    by_contra! hd
    have hhi := cross_pair_actual_upper_of_omitted hG hmin hp hq hne
    dsimp only at hhi
    rw [← hEq,hI,hk] at hhi
    have hc : 1+(12-A.card)≤8 := by omega
    have hChoose := Nat.choose_le_choose 2 hc
    have h8 : Nat.choose 8 2 = 28 := by decide
    have hgap : (5-1)*(1-1)+2*(5-2) < (sources G).card-3 := by rw [hk]; decide
    have hW := away_card_mul_lower hD hp hq hne (r := 5) (d := 1) hr5 hgap
    rw [hk] at hW
    have hlow := hlo hp hq hne
    omega
  have hr3 : ∀ A ∈ B, A.card ≤ 3 := by
    intro A hA
    by_contra! hd
    have hA4 : A.card = 4 := by have h := hr4 A hA; omega
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
      rw [← hEq,hI,hk,hA4] at hhi
      change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 46 at hhi
      omega
  have hW {p q : α} (hp : p ∈ sources G) (hq : q ∈ sources G) (hne : p ≠ q) :
      (away B p q).card + 2*(triples B).card =
        45 + tripleDegree B p + tripleDegree B q := by
    have h := away_card_exact_of_triples hD hr3 hp hq hne
    rw [hk] at h
    have hchoose : Nat.choose 12 2 = 66 := by decide
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
    change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 67 at hu
    omega
  have ht14 : 14 ≤ (triples B).card := by
    obtain ⟨A,hA⟩ := hT
    obtain ⟨p,hp,q,hq,hpq,hpA,hqA,hEq⟩ := pair_representatives_of_triple hG hmin hA
    have hA3 := (Finset.mem_filter.mp hA).2
    have hu := cross_pair_actual_upper_of_omitted hG hmin hp hq hpq
    dsimp only at hu
    rw [← hEq, hA3, hI, hk] at hu
    change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 56 at hu
    have d_p : 1 ≤ tripleDegree B p := Finset.card_pos.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,hpA⟩⟩
    have d_q : 1 ≤ tripleDegree B q := Finset.card_pos.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,hqA⟩⟩
    have h := hW hp hq hpq
    have hl := hlo hp hq hpq
    omega
  obtain ⟨A,hA,hDeg⟩ := exists_high_triple_degree_sum_twelve hD hr3 hk ht14
  have hA3 := (Finset.mem_filter.mp hA).2
  have hDegEq := match_triple_degree_sum_to_links hD hA
  have hLinkEq := linkEdges_card_eq_linkTriples hD hA
  have hLink8 : 8 ≤ (linkEdges B A).card := by omega
  obtain ⟨p,hp,q,hq,hpq,hpA,hqA,hEq⟩ := pair_representatives_of_triple hG hmin hA
  let E := sources G \ A
  let K := compressPair G p q (starLeaf G p) (starLeaf G q)
  let f := signature K
  let P := blockLinks (sources G) B A
  have hES : E.card = 9 := by
    have hh := Finset.card_sdiff_add_card_eq_card (hD.1 A (Finset.mem_filter.mp hA).1).1
    change E.card + A.card = (sources G).card at hh
    omega
  have hsub : linkEdges B A ⊆ P := by
    intro e he
    obtain ⟨heS,he2,T,hT,v,hV,heT⟩ := link_edge_data hD hA he
    exact mem_blockLinks.mpr ⟨heS,he2,T,(Finset.mem_filter.mp hT).1,heT,⟨v,hV⟩⟩
  have hP8 := hLink8.trans (Finset.card_le_card hsub)
  have hSame : ∀ e ∈ P, e ⊆ E ∧ e.card = 2 ∧ ∀ u ∈ e, ∀ v ∈ e, f u = f v := by
    intro e he
    obtain ⟨hsub,h2,_⟩ := mem_blockLinks.mp he
    exact ⟨hsub,h2,fun u hu v hv =>
      compressed_pair_signatures_eq_of_blockLink hG hmin hp hq hpq hpA hqA hEq he hu hv⟩
  have hlabels := image_card_le_four_of_nine_matchings f hES hP8 hSame
    (card_links_in_subset_le_three_half hD hr3 hA3)
  have hcap := pair_fiber_card_le_pow_block_signatures hG hmin hp hq hpq hEq
  have h5 : (E.image f).card + (isolated G).card ≤ 5 := by omega
  have h32 : (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 32 :=
    hcap.trans (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) h5)
  have hLow := hlo hp hq hpq
  omega

/-- Exactly one isolated point and nonzero forcing require at least thirteen sources. -/
theorem one_isolate_nonzero_sources_ge_thirteen {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1) (hk : 0 < (sources G).card) :
    13 ≤ (sources G).card := by
  have hlo := one_isolate_nonzero_sources_ge_twelve hG hmin hI hk
  by_contra! hcap
  exact one_isolate_excludes_twelve_sources hG hmin hI (by omega)

#print axioms exists_high_triple_degree_sum_twelve
#print axioms one_isolate_excludes_twelve_sources
#print axioms one_isolate_nonzero_sources_ge_thirteen

end FranklForcingFiber
