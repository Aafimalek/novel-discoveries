import Mathlib

namespace FranklHeightSix

variable {α : Type*} [DecidableEq α]

def UnionClosed (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B⦄, A ∈ G → B ∈ G → A ∪ B ∈ G

def NoThreeChain (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C⦄, A ∈ G → B ∈ G → C ∈ G → A ⊂ B → B ⊂ C → False

theorem union_eq_top_of_ne {G : Finset (Finset α)} {T A B : Finset α}
    (hU : UnionClosed G) (hH : NoThreeChain G) (hT : T ∈ G)
    (hTop : ∀ ⦃X⦄, X ∈ G → X ⊆ T)
    (hA : A ∈ G) (hB : B ∈ G) (hAT : A ≠ T) (hAB : A ≠ B) :
    A ∪ B = T := by
  have hAT' : A ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hTop hA, hAT⟩
  have hBA : ¬ B ⊆ A := by
    intro h
    exact hH hB hA hT (Finset.ssubset_iff_subset_ne.mpr ⟨h, Ne.symm hAB⟩) hAT'
  have hAne : A ≠ A ∪ B := by
    intro h
    apply hBA
    simpa only [← h] using (Finset.subset_union_right : B ⊆ A ∪ B)
  by_contra hne
  exact hH hA (hU hA hB) hT
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, hAne⟩)
    (Finset.ssubset_iff_subset_ne.mpr ⟨hTop (hU hA hB), hne⟩)

theorem disjoint_complements {G : Finset (Finset α)} {T A B : Finset α}
    (hU : UnionClosed G) (hH : NoThreeChain G) (hT : T ∈ G)
    (hTop : ∀ ⦃X⦄, X ∈ G → X ⊆ T)
    (hA : A ∈ G) (hB : B ∈ G) (hAT : A ≠ T) (hAB : A ≠ B) :
    Disjoint (T \ A) (T \ B) := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  have hxA' := Finset.mem_sdiff.mp hxA
  have hxB' := Finset.mem_sdiff.mp hxB
  have hxU : x ∈ A ∪ B := by
    rw [union_eq_top_of_ne hU hH hT hTop hA hB hAT hAB]
    exact hxA'.1
  exact (Finset.mem_union.mp hxU).elim hxA'.2 hxB'.2

/-- A finite union-closed family of height at most two has at most T.card + 1
sets, where T is its maximum. -/
theorem card_le_top_card_add_one {G : Finset (Finset α)} {T : Finset α}
    (hU : UnionClosed G) (hH : NoThreeChain G) (hT : T ∈ G)
    (hTop : ∀ ⦃X⦄, X ∈ G → X ⊆ T) : G.card ≤ T.card + 1 := by
  classical
  have hw (A : ↥(G.erase T)) : (T \ (A : Finset α)).Nonempty := by
    have hA := Finset.mem_erase.mp A.property
    apply Finset.sdiff_nonempty.mpr
    intro h
    exact hA.1 (Finset.Subset.antisymm (hTop hA.2) h)
  let f (A : ↥(G.erase T)) : ↥T :=
    ⟨(hw A).choose, (Finset.mem_sdiff.mp (hw A).choose_spec).1⟩
  have hfmem (A : ↥(G.erase T)) : (f A : α) ∈ T \ (A : Finset α) :=
    (hw A).choose_spec
  have hf : Function.Injective f := by
    intro A B heq
    by_contra hne
    have hA := Finset.mem_erase.mp A.property
    have hB := Finset.mem_erase.mp B.property
    have hne' : (A : Finset α) ≠ (B : Finset α) := fun h => hne (Subtype.ext h)
    have hd := disjoint_complements hU hH hT hTop hA.2 hB.2 hA.1 hne'
    exact Finset.disjoint_left.mp hd (hfmem A) (by simpa only [heq] using hfmem B)
  have hcard : (G.erase T).card ≤ T.card := Finset.card_le_card_of_injective hf
  calc
    G.card = (G.erase T).card + 1 := (Finset.card_erase_add_one hT).symm
    _ ≤ T.card + 1 := Nat.add_le_add_right hcard 1

end FranklHeightSix

#print axioms FranklHeightSix.card_le_top_card_add_one
