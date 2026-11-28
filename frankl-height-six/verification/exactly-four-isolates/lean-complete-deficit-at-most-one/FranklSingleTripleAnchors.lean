import FranklMixedGeneralBlocks

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence FranklFinsetTwinQuotient
variable {α : Type*} [DecidableEq α]

/-- A common interface for the raw singleton support recovered below. -/
def FullPairIsolateDeletions (G : Finset (Finset α)) (p q : α) : Prop :=
  isolated G ⊆ starPairMax G p q ∧
  ∀ x ∈ isolated G, starPairMax G p q \ {x} ∈ avoidBoth G (starLeaf G p) (starLeaf G q)

theorem fullPairIsolateDeletions_comm {G : Finset (Finset α)} {p q : α} :
    FullPairIsolateDeletions G p q → FullPairIsolateDeletions G q p := by
  intro h
  unfold FullPairIsolateDeletions at h ⊢
  rw [starPairMax_comm G q p,avoidBoth_comm (G := G) (s := starLeaf G q) (t := starLeaf G p)]
  exact h

theorem linked_nominal_Sauer_capacity {G : Finset (Finset α)} {p q : α}
    {Drop : Finset α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hDrop : LinkedDeletion G (omittedStars G (starPairMax G p q)) Drop)
    {m : ℕ}
    (hV : (((sources G \ omittedStars G (starPairMax G p q)) \ Drop) ∪ isolated G).card ≤ m) :
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 1 + m + m.choose 2 := by
  let K := compressedStarPair G p q
  let R := ground K \ Drop
  let L := traceFamily K R
  obtain ⟨_,hRV,_,hcard,hUC,hH,_⟩ := linkedDeletion_pair_quotient_geometry hG hm hp hq hpq hDrop
  have hR : R.card ≤ m := (Finset.card_le_card hRV).trans hV
  have hCh := Nat.choose_le_choose 2 hR
  have hSauer := FranklHeightThreeSauer.card_le R hUC hH (fun _ h => traceFamily_subset h)
  change L.card ≤ 1 + R.card + R.card.choose 2 at hSauer
  change L.card = (avoidBoth G (starLeaf G p) (starLeaf G q)).card at hcard
  omega

theorem sole_triple_data {G : Finset (Finset α)} {T : Finset α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2)
    (hT : triples (starBlocks G) = {T}) :
    T ⊆ sources G ∧ T.card = 3 ∧
    (starBlocks G).card + 2 = (sources G).card.choose 2 ∧
    (∀ r ∈ T, designDegree (starBlocks G) r + 2 = (sources G).card) ∧
    ∀ r ∈ sources G, r ∉ T → designDegree (starBlocks G) r + 1 = (sources G).card := by
  have hD := starBlocks_pairDesign hG hm
  obtain ⟨h3,_,hN,_⟩ := deficit_le_one_triples_classification hD hDeg
  have hTT : T ∈ triples (starBlocks G) := by rw [hT]; simp
  obtain ⟨hTB,hTc⟩ := Finset.mem_filter.mp hTT
  rw [hT,Finset.card_singleton] at hN
  refine ⟨(hD.1 T hTB).1,hTc,by omega,
    fun r hr => deficit_le_one_degree_of_mem_triple hD hDeg hTT hr,?_⟩
  intro r hrS hrT
  have hDegE := card_containing_add_tripleDegree hD h3 hrS
  have h0 : tripleDegree (starBlocks G) r = 0 := by
    simp [tripleDegree,hT,hrT]
  change designDegree (starBlocks G) r + tripleDegree (starBlocks G) r + 1 = _ at hDegE
  omega

theorem omitted_block_eq_of_contains_anchor_pair {G : Finset (Finset α)} {A : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hAB : A ∈ starBlocks G) (hpA : p ∈ A) (hqA : q ∈ A) :
    omittedStars G (starPairMax G p q) = A := by
  let B := omittedStars G (starPairMax G p q)
  have hBB : B ∈ starBlocks G := Finset.mem_image.mpr
    ⟨starPairMax G p q,starPairMax_mem hp hq hpq,rfl⟩
  obtain ⟨hpB,hqB⟩ := omittedBlock_members hp hq
  obtain ⟨C,_,hUnique⟩ := (starBlocks_pairDesign hG hm).2 p hp q hq hpq
  exact (hUnique B ⟨hBB,hpB,hqB⟩).trans (hUnique A ⟨hAB,hpA,hqA⟩).symm

private theorem singleton_link_deletion {G : Finset (Finset α)} {A : Finset α} {u v : α}
    (huv : u ≠ v) (hlink : ({u,v} : Finset α) ∈ blockLinks (sources G) (starBlocks G) A) :
    LinkedDeletion G A ({u} : Finset α) := by
  have hE := (mem_blockLinks.mp hlink).1
  have hu := hE (Finset.mem_insert_self u {v})
  have hv := hE (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
  refine ⟨Finset.singleton_subset_iff.mpr hu,?_⟩
  intro x hx
  have he : x = u := Finset.mem_singleton.mp hx
  subst x
  exact ⟨v,Finset.mem_sdiff.mpr ⟨hv,by simp [huv.symm]⟩,hlink⟩

/-- One anchor inside the unique triple and one outside: ordinary
omitted pair, one independent mate merge, physical singleton holes. -/
theorem sole_triple_cross_anchor {G : Finset (Finset α)} {T : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2)
    (hT : triples (starBlocks G) = {T})
    (hpT : p ∈ T) (hqS : q ∈ sources G) (hqT : q ∉ T) :
    omittedStars G (starPairMax G p q) = {p,q} ∧
    FullPairIsolateDeletions G p q ∧
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤
      1 + ((sources G).card + 1) + ((sources G).card + 1).choose 2 := by
  classical
  let k := (sources G).card
  let A := omittedStars G (starPairMax G p q)
  obtain ⟨hTS,hTc,hN,hDyes,hDno⟩ := sole_triple_data hG hm hDeg hT
  have hpS := hTS hpT
  have hpq : p ≠ q := fun e => hqT (e ▸ hpT)
  have hD := starBlocks_pairDesign hG hm
  have h3 := (deficit_le_one_triples_classification hD hDeg).1
  have hAB : A ∈ starBlocks G := Finset.mem_image.mpr
    ⟨starPairMax G p q,starPairMax_mem hpS hqS hpq,rfl⟩
  obtain ⟨hpA,hqA⟩ := omittedBlock_members hpS hqS
  have hA2 : A.card = 2 := by
    by_contra hn
    have hLo := (hD.1 A hAB).2
    have hHi := h3 A hAB
    have hAc : A.card = 3 := by omega
    have hAT : A ∈ triples (starBlocks G) := Finset.mem_filter.mpr ⟨hAB,hAc⟩
    rw [hT] at hAT
    exact hqT (Finset.mem_singleton.mp hAT ▸ hqA)
  have hA : A = {p,q} := omittedStars_eq_pair_of_card_two hpS hqS hpq hA2
  have hE := Finset.card_erase_add_one hpT
  obtain ⟨u,v,huv,hM⟩ := Finset.card_eq_two.mp (show (T.erase p).card = 2 by omega)
  have hTS' : T = {p,u,v} := by rw [← hM,Finset.insert_erase hpT]
  have hTT : T ∈ triples (starBlocks G) := by rw [hT]; simp
  have hTB := (Finset.mem_filter.mp hTT).1
  have hMate {x : α} (hx : x ∈ ({u,v} : Finset α)) : x ∉ A := by
    obtain ⟨hn,hxT⟩ := Finset.mem_erase.mp (hM.symm ▸ hx)
    have hnq : x ≠ q := fun e => hqT (e ▸ hxT)
    rw [hA]
    simp [hn,hnq]
  have hLink := mates_link_of_triple hG hm (hTS' ▸ hTB) hpA
    (hMate (Finset.mem_insert_self _ _)) (hMate (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) huv
  have hDrop := singleton_link_deletion huv hLink
  let V := ((sources G \ A) \ ({u} : Finset α)) ∪ isolated G
  have hNom := nominal_quotient_card_of_pair_anchor hI hpS hqS hpq hA hDrop
  change V.card + ({u} : Finset α).card = k + 2 at hNom
  rw [Finset.card_singleton] at hNom
  have hVc : V.card = k + 1 := by omega
  have hLow := pair_lower_with_explicit_deficits (dp := 1) (dq := 0) hG hm hI hpS hqS hpq
    (hDyes p hpT) (by simpa using hDno q hqS hqT) (∅ : Finset (α × Finset α)) (by simp)
  simp only [Finset.card_empty,Nat.add_zero] at hLow
  have hBig : 1 + V.card + (V.card - 1).choose 2 <
      (avoidBoth G (starLeaf G p) (starLeaf G q)).card := by
    rw [hVc]
    have hpred : k + 1 - 1 = k := by omega
    rw [hpred]
    change (starBlocks G).card + 2 = k.choose 2 at hN
    change (starBlocks G).card + k + 6 + 1 ≤ _ at hLow
    omega
  exact ⟨hA,linkedDeletion_pair_full_isolate_omissions hG hm hpS hqS hpq hDrop hBig,
    linked_nominal_Sauer_capacity hG hm hpS hqS hpq hDrop hVc.le⟩

/-- Two anchors inside the unique triple: all three stars are omitted,
no linked deletion is needed; the nominal coordinate count is k+1. -/
theorem sole_triple_inside_anchor {G : Finset (Finset α)} {T : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2)
    (hT : triples (starBlocks G) = {T}) (hpT : p ∈ T) (hqT : q ∈ T) (hpq : p ≠ q) :
    omittedStars G (starPairMax G p q) = T ∧
    FullPairIsolateDeletions G p q ∧
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤
      1 + ((sources G).card + 1) + ((sources G).card + 1).choose 2 := by
  classical
  let k := (sources G).card
  let A := omittedStars G (starPairMax G p q)
  obtain ⟨hTS,hTc,hN,hDyes,_⟩ := sole_triple_data hG hm hDeg hT
  have hp := hTS hpT
  have hq := hTS hqT
  have hTT : T ∈ triples (starBlocks G) := by rw [hT]; simp
  have hTB := (Finset.mem_filter.mp hTT).1
  have hA : A = T := omitted_block_eq_of_contains_anchor_pair hG hm hp hq hpq hTB hpT hqT
  have hDrop : LinkedDeletion G A (∅ : Finset α) := by simp [LinkedDeletion]
  let V := ((sources G \ A) \ (∅ : Finset α)) ∪ isolated G
  have hVc : V.card = k + 1 := by
    have hDis : Disjoint (sources G \ T) (isolated G) := by
      apply Finset.disjoint_left.mpr
      exact fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hx).1
    change (((sources G \ A) \ (∅ : Finset α)) ∪ isolated G).card = _
    rw [hA,Finset.sdiff_empty,Finset.card_union_of_disjoint hDis,hI]
    have hE := Finset.card_sdiff_add_card_eq_card hTS
    change (sources G \ T).card + T.card = k at hE
    omega
  have hLow := pair_lower_with_explicit_deficits (dp := 1) (dq := 1) hG hm hI hp hq hpq
    (hDyes p hpT) (hDyes q hqT) (∅ : Finset (α × Finset α)) (by simp)
  simp only [Finset.card_empty,Nat.add_zero] at hLow
  have hBig : 1 + V.card + (V.card - 1).choose 2 <
      (avoidBoth G (starLeaf G p) (starLeaf G q)).card := by
    rw [hVc]
    have hpred : k + 1 - 1 = k := by omega
    rw [hpred]
    change (starBlocks G).card + 2 = k.choose 2 at hN
    change (starBlocks G).card + k + 6 + 1 + 1 ≤ _ at hLow
    omega
  exact ⟨hA,linkedDeletion_pair_full_isolate_omissions hG hm hp hq hpq hDrop hBig,
    linked_nominal_Sauer_capacity hG hm hp hq hpq hDrop hVc.le⟩

#print axioms sole_triple_data
#print axioms sole_triple_cross_anchor
#print axioms sole_triple_inside_anchor
end FranklForcingFiber
