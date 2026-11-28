import FranklTwoMateCollapse

/- Static draft, uncompiled. -/
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

private theorem three_triples_meet_contradicts_degree {B : Finset (Finset α)} {v : α}
    {A C D : Finset α}
    (hA : A ∈ triples B) (hC : C ∈ triples B) (hD : D ∈ triples B)
    (hAC : A ≠ C) (hAD : A ≠ D) (hCD : C ≠ D)
    (hvA : v ∈ A) (hvC : v ∈ C) (hvD : v ∈ D)
    (hdeg : tripleDegree B v ≤ 2) : False := by
  have h3 : ({A,C,D} : Finset (Finset α)).card = 3 := by simp [hAC,hAD,hCD]
  have hSub : ({A,C,D} : Finset (Finset α)) ⊆ (triples B).filter (v ∈ ·) := by
    intro X hX
    simp only [Finset.mem_insert,Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hA,hvA⟩
    · exact Finset.mem_filter.mpr ⟨hC,hvC⟩
    · exact Finset.mem_filter.mpr ⟨hD,hvD⟩
  have hi := Finset.card_le_card hSub
  change ({A,C,D} : Finset (Finset α)).card ≤ tripleDegree B v at hi
  omega

/-- Four pairwise-meeting triples in a pair design of triple degree at
most two are a saturated K4 in the dual triple graph. Every point of
each incident triple lies in precisely one other of the four, and no
further triple meets any of the four. The theorem does not assert
there are no other disjoint triples elsewhere. -/
theorem saturated_four_triples {S : Finset α} {B C : Finset (Finset α)}
    (hD : PairDesign S B) (hC : C ⊆ triples B) (hCc : C.card = 4)
    (hDeg : ∀ v ∈ S, tripleDegree B v ≤ 2)
    (hMeet : ∀ A ∈ C, ∀ D ∈ C, A ≠ D → (A ∩ D).Nonempty) :
    (∀ A ∈ C, ∀ v ∈ A, ∃ D ∈ C, D ≠ A ∧ v ∈ D) ∧
    ∀ T ∈ triples B, T ∉ C → ∀ A ∈ C, Disjoint A T := by
  classical
  have cover : ∀ A ∈ C, ∀ v ∈ A, ∃ D ∈ C, D ≠ A ∧ v ∈ D := by
    intro A hA v hvA
    have hAB := (Finset.mem_filter.mp (hC hA)).1
    have hAc := (Finset.mem_filter.mp (hC hA)).2
    let E := C.erase A
    have hEc : E.card = 3 := by
      have hh : E.card + 1 = C.card := Finset.card_erase_add_one hA
      omega
    have hW (X : ↥E) : (A ∩ X.val).Nonempty := by
      obtain ⟨hne,hX⟩ := Finset.mem_erase.mp X.property
      exact hMeet A hA X.val hX hne.symm
    let g (X : ↥E) := Classical.choose (hW X)
    have hg (X : ↥E) : g X ∈ A ∩ X.val := Classical.choose_spec (hW X)
    have hInj : Set.InjOn g (E.attach : Set ↥E) := by
      intro X _ Y _ he
      apply Subtype.ext
      by_contra hn
      obtain ⟨hXA,hXC⟩ := Finset.mem_erase.mp X.property
      obtain ⟨hYA,hYC⟩ := Finset.mem_erase.mp Y.property
      obtain ⟨hgA,hgX⟩ := Finset.mem_inter.mp (hg X)
      have hgY : g X ∈ Y.val := he.symm ▸ (Finset.mem_inter.mp (hg Y)).2
      have hvS := (hD.1 A hAB).1 hgA
      exact three_triples_meet_contradicts_degree (hC hA) (hC hXC) (hC hYC)
        hXA.symm hYA.symm hn hgA hgX hgY (hDeg (g X) hvS)
    have hSub : E.attach.image g ⊆ A := by
      intro x hx
      obtain ⟨X,_,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_inter.mp (hg X)).1
    have hIc : (E.attach.image g).card = E.card := by
      rw [Finset.card_image_of_injOn hInj,Finset.card_attach]
    have hEq : E.attach.image g = A := Finset.eq_of_subset_of_card_le hSub (by omega)
    have hvG : v ∈ E.attach.image g := hEq.symm ▸ hvA
    obtain ⟨X,_,he⟩ := Finset.mem_image.mp hvG
    obtain ⟨hXA,hXC⟩ := Finset.mem_erase.mp X.property
    exact ⟨X.val,hXC,hXA,he ▸ (Finset.mem_inter.mp (hg X)).2⟩
  refine ⟨cover,?_⟩
  intro T hT hTN A hA
  apply Finset.disjoint_left.mpr
  intro v hvA hvT
  obtain ⟨D,hDC,hDA,hvD⟩ := cover A hA v hvA
  have hAB := (Finset.mem_filter.mp (hC hA)).1
  have hvS := (hD.1 A hAB).1 hvA
  exact three_triples_meet_contradicts_degree (hC hA) (hC hDC) hT hDA.symm
    (fun h => hTN (h ▸ hA)) (fun h => hTN (h ▸ hDC)) hvA hvD hvT (hDeg v hvS)

#print axioms saturated_four_triples
end FranklBlockIncidence
