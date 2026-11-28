import FranklBlockLinkPath

/- Checked by pinned ordinary Lean with warnings as errors. -/
open scoped BigOperators
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- One retained root in each of a finite, disjoint set of linked
regions. No assertion is made that these regions are maximal. -/
theorem transitiveDeletion_of_rooted_link_regions {G : Finset (Finset α)} {A : Finset α}
    (C : Finset (Finset α)) (root : Finset α → α)
    (hDis : (C : Set (Finset α)).PairwiseDisjoint id)
    (hSub : ∀ T ∈ C, T ⊆ sources G \ A)
    (hRoot : ∀ T ∈ C, root T ∈ T)
    (hPath : ∀ T ∈ C, ∀ x ∈ T, BlockLinkPath G A x (root T)) :
    let Drop := C.biUnion (fun T => T.erase (root T))
    TransitivelyLinkedDeletion G A Drop ∧
      Drop.card = ∑ T ∈ C, (T.card - 1) := by
  classical
  let Drop := C.biUnion (fun T => T.erase (root T))
  have hDrop : Drop ⊆ sources G \ A := by
    intro x hx
    obtain ⟨T,hT,hxT⟩ := Finset.mem_biUnion.mp hx
    exact hSub T hT (Finset.mem_of_mem_erase hxT)
  have hKeep {T : Finset α} (hT : T ∈ C) : root T ∉ Drop := by
    intro h
    obtain ⟨U,hU,hrU⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hne,hrU'⟩ := Finset.mem_erase.mp hrU
    by_cases he : T = U
    · subst U
      exact hne rfl
    · exact (Finset.disjoint_left.mp (hDis hT hU he)) (hRoot T hT) hrU'
  have hCertificate : TransitivelyLinkedDeletion G A Drop := by
    refine ⟨hDrop,?_⟩
    intro x hx
    obtain ⟨T,hT,hxT⟩ := Finset.mem_biUnion.mp hx
    exact ⟨root T,Finset.mem_sdiff.mpr ⟨hSub T hT (hRoot T hT),hKeep hT⟩,
      hPath T hT x (Finset.mem_of_mem_erase hxT)⟩
  refine ⟨hCertificate,?_⟩
  have hDropDis : (C : Set (Finset α)).PairwiseDisjoint (fun T => T.erase (root T)) := by
    intro T hT U hU hne
    apply Finset.disjoint_left.mpr
    intro x hxT hxU
    exact (Finset.disjoint_left.mp (hDis hT hU hne))
      (Finset.mem_of_mem_erase hxT) (Finset.mem_of_mem_erase hxU)
  have hCard := Finset.card_biUnion hDropDis
  change Drop.card = ∑ T ∈ C, (T.erase (root T)).card at hCard
  rw [hCard]
  apply Finset.sum_congr rfl
  intro T hT
  exact Finset.card_erase_of_mem (hRoot T hT)

#print axioms transitiveDeletion_of_rooted_link_regions
end FranklForcingFiber
