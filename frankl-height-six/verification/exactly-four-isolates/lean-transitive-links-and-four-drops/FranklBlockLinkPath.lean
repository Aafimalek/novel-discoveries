import FranklDeficitTwoSmall
import Mathlib.Logic.Relation

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence FranklFinsetTwinQuotient
variable {α : Type*} [DecidableEq α]

/-- Two outsiders may be identified by a finite path of actual
block links; they need not have a direct link. -/
def BlockLinkPath (G : Finset (Finset α)) (A : Finset α) (x y : α) : Prop :=
  Relation.ReflTransGen (fun u v => ({u,v} : Finset α) ∈ blockLinks (sources G) (starBlocks G) A) x y

theorem blockLinkPath_of_direct {G : Finset (Finset α)} {A : Finset α} {x y : α}
    (h : ({x,y} : Finset α) ∈ blockLinks (sources G) (starBlocks G) A) : BlockLinkPath G A x y :=
  Relation.ReflTransGen.single h

theorem blockLinkPath_trans {G : Finset (Finset α)} {A : Finset α} {x y z : α}
    (hxy : BlockLinkPath G A x y) (hyz : BlockLinkPath G A y z) : BlockLinkPath G A x z :=
  Relation.ReflTransGen.trans hxy hyz

theorem blockLinkPath_symm {G : Finset (Finset α)} {A : Finset α} {x y : α}
    (h : BlockLinkPath G A x y) : BlockLinkPath G A y x := by
  unfold BlockLinkPath at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v _ hEdge ih =>
    have hr : ({v,u} : Finset α) ∈ blockLinks (sources G) (starBlocks G) A := by
      rw [Finset.pair_comm v u]
      exact hEdge
    exact blockLinkPath_trans (blockLinkPath_of_direct hr) ih

/-- A link path is a genuine equality of occurrence signatures on the
actual compressed pair fiber. -/
theorem compressed_pair_signatures_eq_of_blockLinkPath {G : Finset (Finset α)} {A : Finset α}
    {p q x y : α} (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) (hpA : p ∈ A) (hqA : q ∈ A)
    (hA : A = omittedStars G (starPairMax G p q)) (hPath : BlockLinkPath G A x y) :
    signature (compressedStarPair G p q) x = signature (compressedStarPair G p q) y := by
  unfold BlockLinkPath at hPath
  induction hPath with
  | refl => rfl
  | @tail u v _ hEdge ih =>
    exact ih.trans (compressed_pair_signatures_eq_of_blockLink hG hm hp hq hpq hpA hqA hA
      hEdge (Finset.mem_insert_self u {v}) (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)))

/-- Every deleted outsider reaches some retained outsider by links.
Intermediate path vertices are permitted to be deleted. -/
def TransitivelyLinkedDeletion (G : Finset (Finset α)) (A Drop : Finset α) : Prop :=
  Drop ⊆ sources G \ A ∧
    ∀ x ∈ Drop, ∃ y ∈ (sources G \ A) \ Drop, BlockLinkPath G A x y

theorem transitivelyLinkedDeletion_of_direct {G : Finset (Finset α)} {A Drop : Finset α}
    (h : LinkedDeletion G A Drop) : TransitivelyLinkedDeletion G A Drop := by
  refine ⟨h.1,?_⟩
  intro x hx
  obtain ⟨y,hy,he⟩ := h.2 x hx
  exact ⟨y,hy,blockLinkPath_of_direct he⟩

#print axioms blockLinkPath_symm
#print axioms compressed_pair_signatures_eq_of_blockLinkPath
#print axioms transitivelyLinkedDeletion_of_direct
end FranklForcingFiber
