import FranklElevenStarStructure
import FranklTripleLinks
import FranklFiberSignatures

open scoped BigOperators
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

theorem pair_representatives_of_triple {G : Finset (Finset α)} {A : Finset α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hA : A ∈ triples (starBlocks G)) :
    ∃ p ∈ sources G, ∃ q ∈ sources G, p ≠ q ∧ p ∈ A ∧ q ∈ A ∧
      A = omittedStars G (starPairMax G p q) := by
  obtain ⟨hAB,hA3⟩ := Finset.mem_filter.mp hA
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  have hsub := ((starBlocks_pairDesign hG hmin).1 A hAB).1
  have hpG := hsub hp
  have hqG := hsub hq
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hAB
  exact ⟨p,hpG,q,hqG,hpq,hp,hq,congrArg (omittedStars G)
    (starPairMax_eq_of_omits_pair hG hmin hT hp hq hpq)⟩

/-- One isolate and exactly eleven nontrivial stars cannot occur in a
ground-minimal weak height-six counterexample. -/
theorem one_isolate_excludes_eleven_sources {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1) (hk : (sources G).card = 11) : False := by
  classical
  let B := starBlocks G
  have hD : PairDesign (sources G) B := starBlocks_pairDesign hG hmin
  have h3 : ∀ A ∈ B, A.card ≤ 3 := (one_isolate_eleven_star_structure hG hmin hI hk).1
  have hn0 := partition_card hG hmin
  have hl0 := sources_card_le_leaves hG hmin
  have hn : 23 ≤ (ground G).card := by omega
  have hlo {p q : α} (hp : p ∈ sources G) (hq : q ∈ sources G) (hne : p ≠ q) :
      33 + (away B p q).card ≤ (avoidBoth G (starLeaf G p) (starLeaf G q)).card := by
    have h := leaf_pair_count_with_blocks hG hmin hp hq hne
    change (ground G).card + (sources G).card + (away B p q).card ≤ _ at h
    omega
  have hW {p q : α} (hp : p ∈ sources G) (hq : q ∈ sources G) (hne : p ≠ q) :
      (away B p q).card + 2*(triples B).card =
        36 + tripleDegree B p + tripleDegree B q := by
    have h := away_card_exact_of_triples hD h3 hp hq hne
    rw [hk] at h
    have hchoose : Nat.choose 11 2 = 55 := by decide
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
    change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 56 at hu
    omega
  have ht13 : 13 ≤ (triples B).card := by
    obtain ⟨A,hA⟩ := hT
    obtain ⟨p,hp,q,hq,hpq,hpA,hqA,hEq⟩ := pair_representatives_of_triple hG hmin hA
    have hA3 := (Finset.mem_filter.mp hA).2
    have hu := cross_pair_actual_upper_of_omitted hG hmin hp hq hpq
    dsimp only at hu
    rw [← hEq, hA3, hI, hk] at hu
    change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 46 at hu
    have d_p : 1 ≤ tripleDegree B p := Finset.card_pos.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,hpA⟩⟩
    have d_q : 1 ≤ tripleDegree B q := Finset.card_pos.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,hqA⟩⟩
    have h := hW hp hq hpq
    have hl := hlo hp hq hpq
    omega
  obtain ⟨A,hA,hDeg⟩ := exists_high_triple_degree_sum_eleven hD h3 hk ht13
  have hlinks := linkEdges_card_ge_seven hD hA hDeg
  obtain ⟨p,hp,q,hq,hpq,hpA,hqA,hEq⟩ := pair_representatives_of_triple hG hmin hA
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  let E := sources G \ A
  let K := compressPair G p q (starLeaf G p) (starLeaf G q)
  let f := signature K
  have hES : E.card = 8 := by
    have hh := Finset.card_sdiff_add_card_eq_card (hD.1 A (Finset.mem_filter.mp hA).1).1
    have hA3 := (Finset.mem_filter.mp hA).2
    change E.card + A.card = (sources G).card at hh
    omega
  have hKsub : ∀ Z ∈ K, Z ⊆ E ∪ isolated G := by
    intro Z hZ z hz
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
  have hsame {e : Finset α} (he : e ∈ linkEdges B A) {u v : α} (hu : u ∈ e) (hv : v ∈ e) :
      f u = f v := by
    obtain ⟨hESub,_,T,hT,b,hb,heT⟩ := link_edge_data hD hA he
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
    have huR : u ∈ pairReps G p q :=
      mem_pairReps.mpr ⟨(mem_sources.mp huS).1,
        (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin huS)).2,hpu.symm,hqu.symm⟩
    have hvR : v ∈ pairReps G p q :=
      mem_pairReps.mpr ⟨(mem_sources.mp hvS).1,
        (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin hvS)).2,hpv.symm,hqv.symm⟩
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
        (Finset.mem_filter.mp hT).1 hbT (heT hu) (heT hv) hbu hbv
      have hvu := h1.trans (hL.trans h2.symm)
      change u ∈ X ∩ pairReps G p q ↔ v ∈ X ∩ pairReps G p q
      simp only [Finset.mem_inter,huR,hvR,and_true]
      exact hvu
    ext Z
    change (Z ∈ K.filter (u ∈ ·)) ↔ (Z ∈ K.filter (v ∈ ·))
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1,(hmem h.1).mp h.2⟩,fun h => ⟨h.1,(hmem h.1).mpr h.2⟩⟩
  have hlabels : (E.image f).card ≤ 4 := by
    by_contra! hbad
    have h6 := equal_label_pairs_card_le_six f hES (show 5 ≤ (E.image f).card by omega)
    have hsub : linkEdges B A ⊆ (E.image f).biUnion
        (fun y => (E.filter (fun z => f z = y)).powersetCard 2) := by
      intro D hDb
      obtain ⟨hEs,hD2,_,_,_,_,_⟩ := link_edge_data hD hA hDb
      obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < D.card by omega)
      exact Finset.mem_biUnion.mpr ⟨f u,Finset.mem_image_of_mem f (hEs hu),
        Finset.mem_powersetCard.mpr
          ⟨fun v hv => Finset.mem_filter.mpr ⟨hEs hv,hsame hDb hv hu⟩,hD2⟩⟩
    have he := Finset.card_le_card hsub
    exact (Nat.not_lt_of_ge (he.trans h6)) hlinks
  have hkC : K.card ≤ 32 := by
    have h := family_card_le_pow_signatures hKsub
    have hd : (E.image (signature K)).card + (isolated G).card ≤ 5 := by
      change (E.image f).card + (isolated G).card ≤ 5
      omega
    exact h.trans (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hd)
  have hCard : K.card = (avoidBoth G (starLeaf G p) (starLeaf G q)).card :=
    cross_pair_compress_card hG hmin (mem_sources.mp hp).1 (mem_sources.mp hq).1
      hpq hps hqt hFp hFq
  have hL := hlo hp hq hpq
  omega

/-- A unique isolate and nonzero forcing require at least twelve sources. -/
theorem one_isolate_nonzero_sources_ge_twelve {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1) (hk : 0 < (sources G).card) : 12 ≤ (sources G).card := by
  have hlo := one_isolate_nonzero_sources_ge_eleven hG hmin hI hk
  by_contra! hcap
  exact one_isolate_excludes_eleven_sources hG hmin hI (by omega)

#print axioms one_isolate_excludes_eleven_sources
#print axioms one_isolate_nonzero_sources_ge_twelve

end FranklForcingFiber
