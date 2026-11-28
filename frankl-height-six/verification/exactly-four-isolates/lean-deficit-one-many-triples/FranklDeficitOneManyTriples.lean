import FranklDistinctTripleMixed

/- Checked by pinned ordinary Lean with warnings as errors. -/
open scoped BigOperators
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

noncomputable def tripleSourceUnion (G : Finset (Finset α)) : Finset α :=
  (triples (starBlocks G)).biUnion id

theorem tripleSourceUnion_subset_sources {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G) :
    tripleSourceUnion G ⊆ sources G := by
  intro r hr
  obtain ⟨T,hT,hrT⟩ := Finset.mem_biUnion.mp hr
  exact ((starBlocks_pairDesign hG hm).1 T (Finset.mem_filter.mp hT).1).1 hrT

theorem tripleSourceUnion_card_of_deficit_le_one {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2) :
    (tripleSourceUnion G).card = 3 * (triples (starBlocks G)).card := by
  classical
  let U := triples (starBlocks G)
  have hDis := (deficit_le_one_triples_classification (starBlocks_pairDesign hG hm) hDeg).2.1
  have hc := Finset.card_biUnion hDis
  change (tripleSourceUnion G).card = ∑ A ∈ U, A.card at hc
  rw [hc]
  calc
    _ = ∑ _A ∈ U, 3 := Finset.sum_congr rfl (fun _ hA => (Finset.mem_filter.mp hA).2)
    _ = _ := by simp [U, Finset.sum_const, Nat.mul_comm]

/-- Each source lying in a triple can use two distinct partners from
another triple; isolate singleton holes from the two resulting raw
avoidance maxima give an actual mixed witness in G. -/
theorem mixed_singleton_of_deficit_one_many_triples {G : Finset (Finset α)} {r x : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2)
    (ht : 2 ≤ (triples (starBlocks G)).card)
    (hr : r ∈ tripleSourceUnion G) (hx : x ∈ isolated G) :
    mixedStarOmission G r {x} ∈ G := by
  classical
  let B := starBlocks G
  obtain ⟨P,hP,hrP⟩ := Finset.mem_biUnion.mp hr
  have hEc := Finset.card_erase_add_one hP
  change 2 ≤ (triples B).card at ht
  change ((triples B).erase P).card + 1 = (triples B).card at hEc
  obtain ⟨Q,hQ'⟩ := Finset.card_pos.mp
    (show 0 < ((triples B).erase P).card by omega)
  obtain ⟨hQP,hQ⟩ := Finset.mem_erase.mp hQ'
  have hcQ := (Finset.mem_filter.mp hQ).2
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < Q.card by omega)
  obtain ⟨hrS,haS,hra,hRA,_⟩ :=
    distinct_triple_anchor_links hG hm hDeg hP hQ hQP.symm hrP ha
  obtain ⟨_,hbS,hrb,hRB,_⟩ :=
    distinct_triple_anchor_links hG hm hDeg hP hQ hQP.symm hrP hb
  have hk : 2 ≤ (sources G).card := Finset.one_lt_card.mpr ⟨r,hrS,a,haS,hra⟩
  obtain ⟨hITA,hxA⟩ := exact_four_deficit_le_one_two_triple_anchors hG hm hI hDeg hP hQ hQP.symm hrP ha
  obtain ⟨hITB,hxB⟩ := exact_four_deficit_le_one_two_triple_anchors hG hm hI hDeg hP hQ hQP.symm hrP hb
  obtain ⟨J,hJI,hJD,hJE⟩ := allowed_singleton_of_raw_pair_deletion hrS haS hx hITA (hxA x hx)
  obtain ⟨K,hKI,hKD,hKE⟩ := allowed_singleton_of_raw_pair_deletion hrS hbS hx hITB (hxB x hx)
  have hun {v : α} (hv : v ∈ sources G) := exact_four_unaryAtChosenLeaf hG hm hI hk hv
  have hM := mixedStarOmission_mem_of_two_ordinary_pair_omissions hG hm hrS haS hbS
    hra hrb hab (hun hrS) (hun haS) (hun hbS) hRA hRB hJI hKI hJD hKD
  rw [hJE,hKE,Finset.inter_self] at hM
  exact hM

/-- Conditional contradiction for at least two triple blocks. This is
not the complete deficit-one exclusion: the single-triple branch is
not covered. -/
theorem exact_four_deficit_le_one_not_many_triples {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2)
    (ht : 2 ≤ (triples (starBlocks G)).card) : False := by
  classical
  let B := starBlocks G
  let t := (triples B).card
  let V := tripleSourceUnion G
  have hD := starBlocks_pairDesign hG hm
  obtain ⟨_,_,hN,h3t⟩ := deficit_le_one_triples_classification hD hDeg
  obtain ⟨P,hP,Q,hQ,hPQ⟩ := Finset.one_lt_card.mp (show 1 < (triples B).card by exact ht)
  have hpC := (Finset.mem_filter.mp hP).2
  have hqC := (Finset.mem_filter.mp hQ).2
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < P.card by omega)
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (show 0 < Q.card by omega)
  obtain ⟨hpS,hqS,hpq,_,_⟩ := distinct_triple_anchor_links hG hm hDeg hP hQ hPQ hp hq
  have hpV : p ∈ V := Finset.mem_biUnion.mpr ⟨P,hP,hp⟩
  have hqV : q ∈ V := Finset.mem_biUnion.mpr ⟨Q,hQ,hq⟩
  let K := (V \ {p,q}).product ((isolated G).powersetCard 1)
  have hK : ∀ z ∈ K, z.1 ∈ sources G ∧ z.1 ≠ p ∧ z.1 ≠ q ∧
      z.2 ⊆ isolated G ∧ z.2.Nonempty ∧ mixedStarOmission G z.1 z.2 ∈ G := by
    rintro ⟨r,J⟩ hz
    obtain ⟨hr,hJ⟩ := Finset.mem_product.mp hz
    obtain ⟨hrV,hrn⟩ := Finset.mem_sdiff.mp hr
    have hrp : r ≠ p := fun e => hrn (Finset.mem_insert.mpr (Or.inl e))
    have hrq : r ≠ q := fun e => hrn (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr e))
    obtain ⟨hJI,hJc⟩ := Finset.mem_powersetCard.mp hJ
    obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hJc
    exact ⟨tripleSourceUnion_subset_sources hG hm hrV,hrp,hrq,hJI,
      ⟨x,Finset.mem_singleton_self x⟩,
      mixed_singleton_of_deficit_one_many_triples hG hm hI hDeg ht hrV (hJI (Finset.mem_singleton_self x))⟩
  have hKc : K.card = (3 * t - 2) * 4 := by
    have hsub : ({p,q} : Finset α) ⊆ V := Finset.insert_subset_iff.mpr
      ⟨hpV,Finset.singleton_subset_iff.mpr hqV⟩
    have hVc : V.card = 3 * t := tripleSourceUnion_card_of_deficit_le_one hG hm hDeg
    have hpqc : ({p,q} : Finset α).card = 2 := by simp [hpq]
    change ((V \ {p,q}).product ((isolated G).powersetCard 1)).card = _
    have hOne : (4 : ℕ).choose 1 = 4 := by decide
    calc
      _ = (V \ {p,q}).card * ((isolated G).powersetCard 1).card := Finset.card_product _ _
      _ = _ := by
        rw [Finset.card_sdiff_of_subset hsub,hVc,hpqc,Finset.card_powersetCard,hI,hOne]
  have hdp := deficit_le_one_degree_of_mem_triple hD hDeg hP hp
  have hdq := deficit_le_one_degree_of_mem_triple hD hDeg hQ hq
  have hLow := pair_lower_with_explicit_deficits (dp := 1) (dq := 1)
    hG hm hI hpS hqS hpq hdp hdq K hK
  have hUp := distinct_triple_anchor_capacity hG hm hI hDeg hP hQ hPQ hp hq
  change B.card + 2 * t = (sources G).card.choose 2 at hN
  change 2 ≤ t at ht
  change B.card + (sources G).card + 6 + 1 + 1 + K.card ≤ _ at hLow
  rw [hKc] at hLow
  omega

#print axioms tripleSourceUnion_card_of_deficit_le_one
#print axioms mixed_singleton_of_deficit_one_many_triples
#print axioms exact_four_deficit_le_one_not_many_triples
end FranklForcingFiber
