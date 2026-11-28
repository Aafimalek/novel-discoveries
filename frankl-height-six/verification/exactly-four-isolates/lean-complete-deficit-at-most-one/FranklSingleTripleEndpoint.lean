import FranklSingleTripleAnchors

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- With any outside source available, every source gets the four
mixed singleton witnesses. A source in the triple uses one cross pair
and one inside pair, even when exactly one outside source exists. -/
theorem sole_triple_mixed_singleton_everywhere {G : Finset (Finset α)}
    {T : Finset α} {r x : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2)
    (hT : triples (starBlocks G) = {T})
    (hOut : (sources G \ T).Nonempty)
    (hr : r ∈ sources G) (hx : x ∈ isolated G) :
    mixedStarOmission G r {x} ∈ G := by
  classical
  obtain ⟨hTS,hTc,_,_,_⟩ := sole_triple_data hG hm hDeg hT
  have hkc : T.card ≤ (sources G).card := Finset.card_le_card hTS
  have hUn (v : α) (hv : v ∈ sources G) : UnaryAtChosenLeaf G v :=
    exact_four_unaryAtChosenLeaf hG hm hI (show 2 ≤ (sources G).card by omega) hv
  by_cases hrT : r ∈ T
  · obtain ⟨a,ha⟩ := hOut
    obtain ⟨haS,haT⟩ := Finset.mem_sdiff.mp ha
    have hra : r ≠ a := fun e => haT (e ▸ hrT)
    have hEr := Finset.card_erase_add_one hrT
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < (T.erase r).card by omega)
    obtain ⟨hbr,hbT⟩ := Finset.mem_erase.mp hb
    have hrb : r ≠ b := hbr.symm
    obtain ⟨hA,hFA,_⟩ := sole_triple_cross_anchor hG hm hI hDeg hT hrT haS haT
    obtain ⟨hB,hFB,_⟩ := sole_triple_inside_anchor hG hm hI hDeg hT hrT hbT hrb
    have hMeet : omittedStars G (starPairMax G r a) ∩ omittedStars G (starPairMax G r b) = {r} := by
      rw [hA,hB]
      ext z
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨he | he,hzT⟩
        · exact he
        · exact False.elim (haT (he ▸ hzT))
      · intro he
        exact ⟨Or.inl he,he.symm ▸ hrT⟩
    exact mixed_singleton_of_raw_deletions_intersecting_blocks hG hm hr haS (hTS hbT)
      hra hrb hUn hx hMeet hFA.1 hFB.1 (hFA.2 x hx) (hFB.2 x hx)
  · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
    have hra : r ≠ a := fun e => hrT (e.symm ▸ ha)
    have hrb : r ≠ b := fun e => hrT (e.symm ▸ hb)
    obtain ⟨hA,hFA,_⟩ := sole_triple_cross_anchor hG hm hI hDeg hT ha hr hrT
    obtain ⟨hB,hFB,_⟩ := sole_triple_cross_anchor hG hm hI hDeg hT hb hr hrT
    have hMeet : omittedStars G (starPairMax G r a) ∩ omittedStars G (starPairMax G r b) = {r} := by
      rw [starPairMax_comm G r a,starPairMax_comm G r b,hA,hB]
      ext z
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨he | he,he' | he'⟩
        · exact False.elim (hab (he.symm.trans he'))
        · exact he'
        · exact he
        · exact he
      · intro he
        exact ⟨Or.inr he,Or.inr he⟩
    have hFA' := fullPairIsolateDeletions_comm hFA
    have hFB' := fullPairIsolateDeletions_comm hFB
    exact mixed_singleton_of_raw_deletions_intersecting_blocks hG hm hr (hTS ha) (hTS hb)
      hra hrb hUn hx hMeet hFA'.1 hFB'.1 (hFA'.2 x hx) (hFB'.2 x hx)

/-- Single-triple branch of exactly four isolates and degree ≥k−2. -/
theorem exact_four_deficit_le_one_not_single_triple {G : Finset (Finset α)} {T : Finset α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2)
    (hT : triples (starBlocks G) = {T}) : False := by
  classical
  let k := (sources G).card
  obtain ⟨hTS,hTc,hN,hDyes,hDno⟩ := sole_triple_data hG hm hDeg hT
  have hk : 3 ≤ k := by
    have hsub : T.card ≤ k := Finset.card_le_card hTS
    omega
  by_cases hOut : (sources G \ T).Nonempty
  · obtain ⟨q,hq⟩ := hOut
    obtain ⟨hqS,hqT⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨p,hpT⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
    have hpS := hTS hpT
    have hpq : p ≠ q := fun e => hqT (e ▸ hpT)
    let I := (isolated G).powersetCard 1
    let W := sources G \ {p,q}
    let K := W.product I
    have hK : ∀ z ∈ K, z.1 ∈ sources G ∧ z.1 ≠ p ∧ z.1 ≠ q ∧
        z.2 ⊆ isolated G ∧ z.2.Nonempty ∧ mixedStarOmission G z.1 z.2 ∈ G := by
      rintro ⟨r,J⟩ hz
      obtain ⟨hr,hJ⟩ := Finset.mem_product.mp hz
      obtain ⟨hrS,hrN⟩ := Finset.mem_sdiff.mp hr
      have hrp : r ≠ p := fun e => hrN (Finset.mem_insert.mpr (Or.inl e))
      have hrq : r ≠ q := fun e => hrN (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr e))
      obtain ⟨hJI,hJc⟩ := Finset.mem_powersetCard.mp hJ
      obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hJc
      exact ⟨hrS,hrp,hrq,hJI,⟨x,Finset.mem_singleton_self _⟩,
        sole_triple_mixed_singleton_everywhere hG hm hI hDeg hT ⟨q,Finset.mem_sdiff.mpr ⟨hqS,hqT⟩⟩ hrS (hJI (Finset.mem_singleton_self _))⟩
    have hKc : K.card = (k - 2) * 4 := by
      have hW : W.card = k - 2 := sources_sdiff_pair_card hpS hqS hpq
      have hIc : I.card = 4 := by
        change ((isolated G).powersetCard 1).card = 4
        rw [Finset.card_powersetCard,hI]
        decide
      calc
        _ = W.card * I.card := Finset.card_product _ _
        _ = _ := by rw [hW,hIc]
    have hLo := pair_lower_with_explicit_deficits (dp := 1) (dq := 0)
      hG hm hI hpS hqS hpq (hDyes p hpT) (by simpa using hDno q hqS hqT) K hK
    have hCap := (sole_triple_cross_anchor hG hm hI hDeg hT hpT hqS hqT).2.2
    have hPas : (k + 1).choose 2 = k + k.choose 2 := by
      simpa using Nat.choose_succ_succ' k 1
    change (starBlocks G).card + 2 = k.choose 2 at hN
    change (starBlocks G).card + k + 6 + 1 + 0 + K.card ≤ _ at hLo
    change _ ≤ 1 + (k + 1) + (k + 1).choose 2 at hCap
    rw [hKc] at hLo
    omega
  · have he : sources G \ T = ∅ := by
      by_contra hn
      exact hOut (Finset.nonempty_iff_ne_empty.mpr hn)
    have hST := Finset.sdiff_eq_empty_iff_subset.mp he
    have heq : sources G = T := Finset.Subset.antisymm hST hTS
    have hk3 : (sources G).card = 3 := by rw [heq,hTc]
    obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
    have hLo := pair_lower_with_explicit_deficits (dp := 1) (dq := 1)
      hG hm hI (hTS hp) (hTS hq) hpq (hDyes p hp) (hDyes q hq)
      (∅ : Finset (α × Finset α)) (by simp)
    have hCap := (sole_triple_inside_anchor hG hm hI hDeg hT hp hq hpq).2.2
    have hChoose : (3 : ℕ).choose 2 = 3 := by decide
    have hH : 1 + (3 + 1) + (3 + 1 : ℕ).choose 2 = 11 := by decide
    rw [hk3,hChoose] at hN
    rw [hk3,hH] at hCap
    rw [hk3,Finset.card_empty] at hLo
    omega

#print axioms sole_triple_mixed_singleton_everywhere
#print axioms exact_four_deficit_le_one_not_single_triple
end FranklForcingFiber
