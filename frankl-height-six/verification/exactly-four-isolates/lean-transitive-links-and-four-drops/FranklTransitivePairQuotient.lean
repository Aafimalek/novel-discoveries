import FranklBlockLinkPath

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence FranklFinsetTwinQuotient
variable {α : Type*} [DecidableEq α]

theorem transitiveLinkedDeletion_pair_quotient_geometry {G : Finset (Finset α)} {p q : α}
    {Drop : Finset α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hDrop : TransitivelyLinkedDeletion G (omittedStars G (starPairMax G p q)) Drop) :
    let K := compressedStarPair G p q
    let U := ground K
    let R := U \ Drop
    let A := omittedStars G (starPairMax G p q)
    let V := ((sources G \ A) \ Drop) ∪ isolated G
    let L := traceFamily K R
    Drop ⊆ U ∧ R ⊆ V ∧ ground L = R ∧
      L.card = (avoidBoth G (starLeaf G p) (starLeaf G q)).card ∧
      (∀ ⦃B C⦄, B ∈ L → C ∈ L → B ∪ C ∈ L) ∧
      FranklHeightThreeSauer.NoFourChain L ∧
      ∀ x ∈ U \ R, ∃ y ∈ R \ isolated G, ∀ X ∈ K, x ∈ X ↔ y ∈ X := by
  classical
  let K := compressedStarPair G p q
  let U := ground K
  let R := U \ Drop
  let A := omittedStars G (starPairMax G p q)
  let V := ((sources G \ A) \ Drop) ∪ isolated G
  let L := traceFamily K R
  have hGround : U = (sources G \ A) ∪ (isolated G ∩ starPairMax G p q) :=
    compressedStarPair_ground_eq_centers_union_present_isolates hG hm hp hq hpq
  have hCenterU : sources G \ A ⊆ U := by rw [hGround]; exact Finset.subset_union_left
  have hDropU : Drop ⊆ U := hDrop.1.trans hCenterU
  have hRV : R ⊆ V := by
    intro x hx
    obtain ⟨hxU,hxn⟩ := Finset.mem_sdiff.mp hx
    rw [hGround] at hxU
    rcases Finset.mem_union.mp hxU with hs | hi
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hs,hxn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).1
  have hTwinI : ∀ x ∈ U \ R, ∃ y ∈ R \ isolated G, ∀ X ∈ K, x ∈ X ↔ y ∈ X := by
    intro x hx
    obtain ⟨hxU,hxn⟩ := Finset.mem_sdiff.mp hx
    have hxD : x ∈ Drop := by by_contra hn; exact hxn (Finset.mem_sdiff.mpr ⟨hxU,hn⟩)
    obtain ⟨y,hy,hlink⟩ := hDrop.2 x hxD
    obtain ⟨hyA,hyD⟩ := Finset.mem_sdiff.mp hy
    have hyR : y ∈ R := Finset.mem_sdiff.mpr ⟨hCenterU hyA,hyD⟩
    have hyI : y ∉ isolated G := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mp hyA).1
    refine ⟨y,Finset.mem_sdiff.mpr ⟨hyR,hyI⟩,?_⟩
    intro X hX
    obtain ⟨hpA,hqA⟩ := omittedBlock_members hp hq
    have hSig := compressed_pair_signatures_eq_of_blockLinkPath hG hm hp hq hpq hpA hqA rfl hlink
    have hEq : (K.filter (x ∈ ·)) = K.filter (y ∈ ·) := hSig
    constructor
    · intro hxX
      have hx' : X ∈ K.filter (x ∈ ·) := Finset.mem_filter.mpr ⟨hX,hxX⟩
      have hy' : X ∈ K.filter (y ∈ ·) := hEq ▸ hx'
      exact (Finset.mem_filter.mp hy').2
    · intro hyX
      have hy' : X ∈ K.filter (y ∈ ·) := Finset.mem_filter.mpr ⟨hX,hyX⟩
      have hx' : X ∈ K.filter (x ∈ ·) := hEq.symm ▸ hy'
      exact (Finset.mem_filter.mp hx').2
  have hTwin : HasRetainedTwins K U R := by
    intro x hx
    obtain ⟨y,hy,hh⟩ := hTwinI x hx
    exact ⟨y,(Finset.mem_sdiff.mp hy).1,hh⟩
  have hKSub : ∀ C ∈ K, C ⊆ U := fun _ hC => subset_ground hC
  have hKL : L.card = K.card := traceFamily_card_eq hKSub hTwin
  have hKUC := compressedStarPair_unionClosed (p := p) (q := q) hG
  have hKnoFour := compressedStarPair_noFourChain hG hm hp hq hpq
  have hU : U ∈ K := ground_mem_unionClosed hKUC (compressedStarPair_nonempty hG hm hp hq hpq)
  have hRL : R ∈ L := traceFamily_contains_support Finset.sdiff_subset hU
  have hGroundL : ground L = R := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨B,hB,hxB⟩ := exists_mem_of_mem_ground hx
      exact traceFamily_subset hB hxB
    · exact subset_ground hRL
  exact ⟨hDropU,hRV,hGroundL,hKL.trans (compressedStarPair_card hG hm hp hq hpq),
    traceFamily_unionClosed hKUC,traceFamily_noFourChain hKSub hTwin hKnoFour,hTwinI⟩

/-- No missing quotient coordinates or non-singleton atom can survive
above the atom-sensitive threshold calculated on the nominal quotient. -/
theorem transitiveLinkedDeletion_pair_full_isolate_omissions {G : Finset (Finset α)} {p q : α}
    {Drop : Finset α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hDrop : TransitivelyLinkedDeletion G (omittedStars G (starPairMax G p q)) Drop)
    (hLarge :
      let V := ((sources G \ omittedStars G (starPairMax G p q)) \ Drop) ∪ isolated G
      1 + V.card + (V.card - 1).choose 2 <
        (avoidBoth G (starLeaf G p) (starLeaf G q)).card) :
    isolated G ⊆ starPairMax G p q ∧
    ∀ x ∈ isolated G, starPairMax G p q \ {x} ∈ avoidBoth G (starLeaf G p) (starLeaf G q) := by
  classical
  let K := compressedStarPair G p q
  let U := ground K
  let R := U \ Drop
  let V := ((sources G \ omittedStars G (starPairMax G p q)) \ Drop) ∪ isolated G
  let L := traceFamily K R
  obtain ⟨_,hRV,hground,hcard,hUC,hH,hT⟩ :=
    transitiveLinkedDeletion_pair_quotient_geometry hG hm hp hq hpq hDrop
  change R ⊆ V at hRV
  change ground L = R at hground
  change L.card = (avoidBoth G (starLeaf G p) (starLeaf G q)).card at hcard
  change 1 + V.card + (V.card - 1).choose 2 <
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card at hLarge
  have hRcard := Finset.card_le_card hRV
  have hVR : R = V := by
    apply Finset.eq_of_subset_of_card_le hRV
    by_contra hnot
    have hle : R.card ≤ V.card - 1 := by omega
    have hSauer := FranklHeightThreeSauer.card_le R hUC hH (fun _ h => traceFamily_subset h)
    change L.card ≤ 1 + R.card + R.card.choose 2 at hSauer
    have hC := Nat.choose_le_choose 2 hle
    omega
  have hIR : isolated G ⊆ R := by rw [hVR]; exact Finset.subset_union_right
  have hIT : isolated G ⊆ starPairMax G p q := by
    intro x hx
    exact (isolate_mem_trueSupport_iff_present hG hm hp hq hpq hx).mp
      ((Finset.mem_sdiff.mp (hIR hx)).1)
  refine ⟨hIT,?_⟩
  intro x hx
  have hxR := hIR hx
  have hlarge' : 1 + (ground L).card + ((ground L).card - 1).choose 2 < L.card := by
    rw [hground,hVR,hcard]
    exact hLarge
  have hLne : L.Nonempty := Finset.card_pos.mp (by omega)
  have hxD := trueComplement_singleton_mem_of_large_card hUC hLne hH hlarge'
    (show x ∈ ground L by rw [hground]; exact hxR)
  have hxM := ((complementOn_mem_iff (fun _ h => subset_ground h)).mp hxD).2
  change ground L \ {x} ∈ L at hxM
  rw [hground] at hxM
  have hxIR : ({x} : Finset α) ⊆ isolated G := Finset.singleton_subset_iff.mpr hx
  have hxKR : ({x} : Finset α) ⊆ R := hxIR.trans hIR
  have hxU : U \ {x} ∈ K := top_sdiff_mem_of_trace
    (fun _ h => subset_ground h) Finset.sdiff_subset hxIR hxKR hT hxM
  have hxOrig : ({x} : Finset α) ∈ starPairTrueComplement G p q :=
    (complementOn_mem_iff (fun _ h => subset_ground h)).mpr
      ⟨Finset.singleton_subset_iff.mpr ((Finset.mem_sdiff.mp hxR).1),hxU⟩
  exact raw_pairMax_sdiff_mem_of_isolate_atom_omission hG hm hp hq hpq hxIR hxOrig


#print axioms transitiveLinkedDeletion_pair_quotient_geometry
#print axioms transitiveLinkedDeletion_pair_full_isolate_omissions
end FranklForcingFiber
