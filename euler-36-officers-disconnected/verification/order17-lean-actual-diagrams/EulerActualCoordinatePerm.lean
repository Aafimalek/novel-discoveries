import EulerActualPublishedDiagrams
import Mathlib.Data.Fintype.EquivFin

namespace LatinGap
open EulerAllUsedDiagrams

def archivedPermutationCheck (p : List Nat) : Bool :=
  (indices.all fun i => p.getD i 0 < 4) &&
    (indices.all fun i => indices.all fun j =>
      (p.getD i 0 != p.getD j 0) || i == j)

private theorem all_archivedPermutationChecks :
    allPermutations.all archivedPermutationCheck = true := by decide +kernel

private theorem coord_mem_indices (i : Coord) : i.val ∈ indices := by fin_cases i <;> decide

theorem archivedPermutation_bounds {p : List Nat} (h : p ∈ allPermutations)
    (i : Coord) : p.getD i.val 0 < 4 := by
  have check := List.all_eq_true.mp all_archivedPermutationChecks _ h
  have fst := (Bool.and_eq_true_iff.mp check).1
  exact decide_eq_true_eq.mp (List.all_eq_true.mp fst _ (coord_mem_indices i))

noncomputable def archivedCoordinatePerm (p : List Nat) (h : p ∈ allPermutations) :
    Coord ≃ Coord := by
  let f (i : Coord) : Coord := ⟨p.getD i.val 0,archivedPermutation_bounds h i⟩
  have inj : Function.Injective f := by
    intro i j eq
    have check := List.all_eq_true.mp all_archivedPermutationChecks _ h
    have snd := (Bool.and_eq_true_iff.mp check).2
    have c := List.all_eq_true.mp (List.all_eq_true.mp snd _ (coord_mem_indices i))
      _ (coord_mem_indices j)
    have same : p.getD i.val 0 = p.getD j.val 0 := congrArg Fin.val eq
    rw [same] at c
    exact Fin.ext (by simpa using c)
  exact Equiv.ofBijective f ⟨inj, Finite.surjective_of_injective inj⟩

theorem archivedCoordinatePerm_val (p : List Nat) (h : p ∈ allPermutations)
    (i : Coord) : (archivedCoordinatePerm p h i).val = p.getD i.val 0 := rfl

/-- The minimizing archive permutation really permutes coordinates;
the corresponding four outer words remain members of the actual design. -/
theorem archived_permutation_realizes_outer {E : Design 6} (lin : Linear E)
    (sat : Saturated E) (zero : (fun _ => 0) ∈ E)
    (low : ∀ j, freq E (j,0) = 2) (U : Coord → Word 6)
    (hw : ∀ i, U i ∈ E ∧ U i i = 0 ∧ ∀ j ≠ i, U i j ≠ 0)
    (p : List Nat) (hp : p ∈ allPermutations) :
    let k := archivedCoordinatePerm p hp
    let F := renameDesign k (fun _ => Equiv.refl _) E
    let V (i : Coord) := renameWords k (fun _ => Equiv.refl _) (U (k i))
    Linear F ∧ Saturated F ∧ F.card = E.card ∧ (fun _ => 0) ∈ F ∧
      (∀ j, freq F (j,0) = 2) ∧
      (∀ i, V i ∈ F ∧ V i i = 0 ∧ ∀ j ≠ i, V i j ≠ 0) ∧
      (∀ i j : Coord, (V i j).val = value (ofColumns (outerColumns U))
        (p.getD i.val 0) (p.getD j.val 0)) := by
  dsimp only
  let k := archivedCoordinatePerm p hp
  let lab : Coord → Fin 6 ≃ Fin 6 := fun _ => Equiv.refl _
  refine ⟨renameDesign_linear lin k lab,renameDesign_saturated sat k lab,
    renameDesign_card k lab E,?_,?_,?_,?_⟩
  · exact Finset.mem_map.mpr ⟨_,zero,rfl⟩
  · intro j
    exact (renameDesign_freq k lab E j 0).trans (low (k j))
  · intro i
    refine ⟨Finset.mem_map.mpr ⟨_,(hw (k i)).1,rfl⟩,(hw (k i)).2.1,?_⟩
    intro j ne
    exact (hw (k i)).2.2 (k j) (k.injective.ne ne)
  · intro i j
    have e := outerColumns_value U (fun g => (hw g).2.1) (k i) (k j)
    rw [archivedCoordinatePerm_val,archivedCoordinatePerm_val] at e
    exact e.symm

#print axioms archivedCoordinatePerm
#print axioms archived_permutation_realizes_outer
end LatinGap
