import FranklDeficitTwoFourDrop

/- Checked by pinned ordinary Lean with warnings as errors. -/
open scoped BigOperators
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- A group of outsiders with an actual link for each distinct pair. -/
def BlockLinkClique (G : Finset (Finset α)) (A E : Finset α) : Prop :=
  E ⊆ sources G \ A ∧
    ∀ u ∈ E, ∀ v ∈ E, u ≠ v →
      ({u,v} : Finset α) ∈ blockLinks (sources G) (starBlocks G) A

theorem blockLinkClique_of_incident_block {G : Finset (Finset α)} {A B E : Finset α} {r : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hB : B ∈ starBlocks G) (hrA : r ∈ A) (hrB : r ∈ B)
    (hEB : E ⊆ B) (hEA : Disjoint E A) :
    BlockLinkClique G A E := by
  have hBS := ((starBlocks_pairDesign hG hm).1 B hB).1
  have hE : E ⊆ sources G \ A := fun _ hx =>
    Finset.mem_sdiff.mpr ⟨hBS (hEB hx),(Finset.disjoint_left.mp hEA) hx⟩
  refine ⟨hE,?_⟩
  intro u hu v hv huv
  have hSub : ({u,v} : Finset α) ⊆ E :=
    Finset.insert_subset_iff.mpr ⟨hu,Finset.singleton_subset_iff.mpr hv⟩
  exact mem_blockLinks.mpr
    ⟨hSub.trans hE,by simp [huv],B,hB,hSub.trans hEB,r,Finset.mem_inter.mpr ⟨hrA,hrB⟩⟩

theorem transitiveDeletion_of_link_cliques {G : Finset (Finset α)} {A : Finset α}
    (C : Finset (Finset α)) (hDis : (C : Set (Finset α)).PairwiseDisjoint id)
    (hNe : ∀ E ∈ C, E.Nonempty) (hClique : ∀ E ∈ C, BlockLinkClique G A E) :
    ∃ Drop, TransitivelyLinkedDeletion G A Drop ∧ Drop.card = ∑ E ∈ C, (E.card - 1) := by
  classical
  by_cases he : C = ∅
  · subst C
    exact ⟨∅,by simp [TransitivelyLinkedDeletion],by simp⟩
  obtain ⟨E₀,hE₀⟩ := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨x₀,_⟩ := hNe E₀ hE₀
  let r (E : Finset α) := if h : E ∈ C then Classical.choose (hNe E h) else x₀
  have hr : ∀ E ∈ C, r E ∈ E := by
    intro E hE
    simpa only [r,dite_eq_left hE] using Classical.choose_spec (hNe E hE)
  have hPaths : ∀ E ∈ C, ∀ x ∈ E, BlockLinkPath G A x (r E) := by
    intro E hE x hx
    by_cases he : x = r E
    · rw [he]
      exact Relation.ReflTransGen.refl
    · exact blockLinkPath_of_direct ((hClique E hE).2 x hx (r E) (hr E hE) he)
  have hDrop := transitiveDeletion_of_rooted_link_regions C r hDis
    (fun E hE => (hClique E hE).1) hr hPaths
  exact ⟨C.biUnion (fun E => E.erase (r E)),hDrop⟩

/-- Two disjoint nonempty cliques supply the sum of their independent
deletions. This will be applied to two three-point quad mate groups. -/
theorem transitiveDeletion_of_two_link_cliques {G : Finset (Finset α)} {A E F : Finset α}
    (hE : BlockLinkClique G A E) (hF : BlockLinkClique G A F)
    (hEN : E.Nonempty) (hFN : F.Nonempty) (hEF : Disjoint E F) :
    ∃ Drop, TransitivelyLinkedDeletion G A Drop ∧
      Drop.card = (E.card - 1) + (F.card - 1) := by
  classical
  have hne : E ≠ F := by
    obtain ⟨x,hx⟩ := hEN
    intro he
    exact (Finset.disjoint_left.mp hEF) hx (he ▸ hx)
  have hDis : (({E,F} : Finset (Finset α)) : Set (Finset α)).PairwiseDisjoint id := by
    intro X hX Y hY hXY
    change X ∈ ({E,F} : Finset (Finset α)) at hX
    change Y ∈ ({E,F} : Finset (Finset α)) at hY
    simp only [Finset.mem_insert,Finset.mem_singleton] at hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact False.elim (hXY rfl)
    · exact hEF
    · exact hEF.symm
    · exact False.elim (hXY rfl)
  have forall_two (R : Finset α → Prop) (h1 : R E) (h2 : R F) : ∀ X ∈ ({E,F} : Finset (Finset α)), R X := by
    intro X hX
    simp only [Finset.mem_insert,Finset.mem_singleton] at hX
    rcases hX with rfl | rfl
    · exact h1
    · exact h2
  obtain ⟨Drop,hDrop,hc⟩ := transitiveDeletion_of_link_cliques {E,F} hDis
    (forall_two Finset.Nonempty hEN hFN) (forall_two (BlockLinkClique G A) hE hF)
  refine ⟨Drop,hDrop,?_⟩
  rw [hc,Finset.sum_insert (by simp [hne]),Finset.sum_singleton]

/-- Three disjoint nonempty cliques supply three independent rooted
components. This will be applied to one quad group and two triple groups. -/
theorem transitiveDeletion_of_three_link_cliques {G : Finset (Finset α)} {A E F H : Finset α}
    (hE : BlockLinkClique G A E) (hF : BlockLinkClique G A F) (hH : BlockLinkClique G A H)
    (hEN : E.Nonempty) (hFN : F.Nonempty) (hHN : H.Nonempty)
    (hEF : Disjoint E F) (hEH : Disjoint E H) (hFH : Disjoint F H) :
    ∃ Drop, TransitivelyLinkedDeletion G A Drop ∧
      Drop.card = (E.card - 1) + ((F.card - 1) + (H.card - 1)) := by
  classical
  have ne {X Y : Finset α} (hX : X.Nonempty) (hD : Disjoint X Y) : X ≠ Y := by
    obtain ⟨x,hx⟩ := hX
    intro he
    exact (Finset.disjoint_left.mp hD) hx (he ▸ hx)
  have hEFn := ne hEN hEF
  have hEHn := ne hEN hEH
  have hFHn := ne hFN hFH
  have hDis : (({E,F,H} : Finset (Finset α)) : Set (Finset α)).PairwiseDisjoint id := by
    intro X hX Y hY hXY
    change X ∈ ({E,F,H} : Finset (Finset α)) at hX
    change Y ∈ ({E,F,H} : Finset (Finset α)) at hY
    simp only [Finset.mem_insert,Finset.mem_singleton] at hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact False.elim (hXY rfl)
    · exact hEF
    · exact hEH
    · exact hEF.symm
    · exact False.elim (hXY rfl)
    · exact hFH
    · exact hEH.symm
    · exact hFH.symm
    · exact False.elim (hXY rfl)
  have forall_three (R : Finset α → Prop) (h1 : R E) (h2 : R F) (h3 : R H) :
      ∀ X ∈ ({E,F,H} : Finset (Finset α)), R X := by
    intro X hX
    simp only [Finset.mem_insert,Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  obtain ⟨Drop,hDrop,hc⟩ := transitiveDeletion_of_link_cliques {E,F,H} hDis
    (forall_three Finset.Nonempty hEN hFN hHN) (forall_three (BlockLinkClique G A) hE hF hH)
  refine ⟨Drop,hDrop,?_⟩
  rw [hc,Finset.sum_insert (by simp [hEFn,hEHn]),Finset.sum_insert (by simp [hFHn]),
    Finset.sum_singleton]

#print axioms blockLinkClique_of_incident_block
#print axioms transitiveDeletion_of_link_cliques
#print axioms transitiveDeletion_of_two_link_cliques
#print axioms transitiveDeletion_of_three_link_cliques
end FranklForcingFiber
