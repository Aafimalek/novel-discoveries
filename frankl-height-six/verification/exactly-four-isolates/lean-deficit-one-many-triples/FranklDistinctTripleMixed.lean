import FranklDeficitOneActualAnchors
import FranklFourAllPairHoleInter

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence FranklFinsetTwinQuotient
variable {α : Type*} [DecidableEq α]

/-- Explicit geometry for distinct triple anchors: their common block
is ordinary and the two mate pairs supply two independent deletions. -/
theorem distinct_triple_anchor_links {G : Finset (Finset α)} {P Q : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2)
    (hP : P ∈ triples (starBlocks G)) (hQ : Q ∈ triples (starBlocks G))
    (hPQ : P ≠ Q) (hp : p ∈ P) (hq : q ∈ Q) :
    p ∈ sources G ∧ q ∈ sources G ∧ p ≠ q ∧
    omittedStars G (starPairMax G p q) = {p,q} ∧
    ∃ Drop, LinkedDeletion G (omittedStars G (starPairMax G p q)) Drop ∧ Drop.card = 2 := by
  classical
  have hD := starBlocks_pairDesign hG hm
  obtain ⟨h3,hDisjoint,_,_⟩ := deficit_le_one_triples_classification hD hDeg
  obtain ⟨hPB,hPc⟩ := Finset.mem_filter.mp hP
  obtain ⟨hQB,hQc⟩ := Finset.mem_filter.mp hQ
  have hpS := (hD.1 P hPB).1 hp
  have hqS := (hD.1 Q hQB).1 hq
  have hDis : Disjoint P Q := hDisjoint hP hQ hPQ
  have hpq : p ≠ q := fun e => (Finset.disjoint_left.mp hDis) hp (e.symm ▸ hq)
  let A := omittedStars G (starPairMax G p q)
  have hAB : A ∈ starBlocks G := Finset.mem_image.mpr
    ⟨starPairMax G p q,starPairMax_mem hpS hqS hpq,rfl⟩
  obtain ⟨hpA,hqA⟩ := omittedBlock_members hpS hqS
  have hA2 : A.card = 2 := by
    by_contra hn
    have hLo := (hD.1 A hAB).2
    have hHi := h3 A hAB
    have hc : A.card = 3 := by omega
    have hAT : A ∈ triples (starBlocks G) := Finset.mem_filter.mpr ⟨hAB,hc⟩
    have hAP : A = P := by
      by_contra hne
      exact (Finset.disjoint_left.mp (hDisjoint hAT hP hne)) hpA hp
    have hqP : q ∈ P := by rw [← hAP]; exact hqA
    exact (Finset.disjoint_left.mp hDis) hqP hq
  have hA : A = {p,q} := omittedStars_eq_pair_of_card_two hpS hqS hpq hA2
  refine ⟨hpS,hqS,hpq,hA,?_⟩
  have pair_through {T : Finset α} {r : α} (hT : T.card = 3) (hr : r ∈ T) :
      ∃ u v, u ≠ v ∧ T.erase r = {u,v} ∧ T = {r,u,v} := by
    have hce := Finset.card_erase_add_one hr
    have h2 : (T.erase r).card = 2 := by omega
    obtain ⟨u,v,huv,hmates⟩ := Finset.card_eq_two.mp h2
    exact ⟨u,v,huv,hmates,by rw [← hmates,Finset.insert_erase hr]⟩
  obtain ⟨u,v,huv,hPE,hPt⟩ := pair_through hPc hp
  obtain ⟨w,z,hwz,hQE,hQt⟩ := pair_through hQc hq
  have hpMate {x : α} (hx : x ∈ ({u,v} : Finset α)) : x ∉ A := by
    obtain ⟨hn,hxP⟩ := Finset.mem_erase.mp (hPE.symm ▸ hx)
    have hnq : x ≠ q := fun e => (Finset.disjoint_left.mp hDis) hxP (e.symm ▸ hq)
    rw [hA]
    simp [hn,hnq]
  have hqMate {x : α} (hx : x ∈ ({w,z} : Finset α)) : x ∉ A := by
    obtain ⟨hn,hxQ⟩ := Finset.mem_erase.mp (hQE.symm ▸ hx)
    have hnp : x ≠ p := fun e => (Finset.disjoint_left.mp hDis) (e.symm ▸ hp) hxQ
    rw [hA]
    simp [hn,hnp]
  have hL := mates_link_of_triple hG hm (hPt ▸ hPB) hpA
    (hpMate (Finset.mem_insert_self _ _)) (hpMate (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) huv
  have hR := mates_link_of_triple hG hm (hQt ▸ hQB) hqA
    (hqMate (Finset.mem_insert_self _ _)) (hqMate (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) hwz
  have hMDis : Disjoint ({u,v} : Finset α) {w,z} := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.disjoint_left.mp hDis) (Finset.mem_of_mem_erase (hPE.symm ▸ hx))
      (Finset.mem_of_mem_erase (hQE.symm ▸ hy))
  exact ⟨{u,w},linkedDeletion_of_two_disjoint_links hL hR hMDis⟩

theorem distinct_triple_anchor_capacity {G : Finset (Finset α)} {P Q : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2)
    (hP : P ∈ triples (starBlocks G)) (hQ : Q ∈ triples (starBlocks G))
    (hPQ : P ≠ Q) (hp : p ∈ P) (hq : q ∈ Q) :
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤
      1 + (sources G).card + (sources G).card.choose 2 := by
  obtain ⟨hpS,hqS,hpq,hA,Drop,hDrop,hDropC⟩ := distinct_triple_anchor_links hG hm hDeg hP hQ hPQ hp hq
  let K := compressedStarPair G p q
  let R := ground K \ Drop
  let V := ((sources G \ omittedStars G (starPairMax G p q)) \ Drop) ∪ isolated G
  let L := traceFamily K R
  obtain ⟨_,hRV,_,hcard,hUC,hH,_⟩ := linkedDeletion_pair_quotient_geometry hG hm hpS hqS hpq hDrop
  have hc := nominal_quotient_card_of_pair_anchor hI hpS hqS hpq hA hDrop
  change V.card + Drop.card = (sources G).card + 2 at hc
  have hV : V.card = (sources G).card := by omega
  have hRVc : R.card ≤ V.card := Finset.card_le_card hRV
  have hR : R.card ≤ (sources G).card := by omega
  have hCh := Nat.choose_le_choose 2 hR
  have hSauer := FranklHeightThreeSauer.card_le R hUC hH (fun _ h => traceFamily_subset h)
  change L.card ≤ 1 + R.card + R.card.choose 2 at hSauer
  change L.card = (avoidBoth G (starLeaf G p) (starLeaf G q)).card at hcard
  omega

/-- Converse for an isolate singleton: a witnessed physical omission
with full isolate support yields the allowed relative/absolute hole. -/
theorem allowed_singleton_of_raw_pair_deletion {G : Finset (Finset α)} {p q x : α}
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hx : x ∈ isolated G)
    (hIT : isolated G ⊆ starPairMax G p q)
    (hxF : starPairMax G p q \ {x} ∈ avoidBoth G (starLeaf G p) (starLeaf G q)) :
    AllowedPairIsolateHole G p q {x} := by
  let J : Finset α := {x}
  let T := starPairMax G p q
  let R := pairReps G p q
  have hxR : x ∈ R := isolates_subset_pairReps_of_sources hp hq hx
  have hjC : J ⊆ ground (compressedStarPair G p q) := by
    rw [compressedStarPair_ground_eq_inter]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hIT hx,hxR⟩)
  have hjF : ground (compressedStarPair G p q) \ J ∈ compressedStarPair G p q := by
    rw [compressedStarPair_ground_eq_inter]
    refine Finset.mem_image.mpr ⟨T \ J,hxF,?_⟩
    exact Finset.sdiff_inter_right_comm T J R
  have hjD : J ∈ starPairTrueComplement G p q :=
    (complementOn_mem_iff (fun _ h => subset_ground h)).mpr ⟨hjC,hjF⟩
  refine ⟨J,Finset.singleton_subset_iff.mpr hx,hjD,?_⟩
  change (isolated G \ T) ∪ J = J
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hIT,Finset.empty_union]

#print axioms distinct_triple_anchor_links
#print axioms distinct_triple_anchor_capacity
#print axioms allowed_singleton_of_raw_pair_deletion
end FranklForcingFiber
