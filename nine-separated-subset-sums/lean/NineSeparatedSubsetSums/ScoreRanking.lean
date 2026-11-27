import NineSeparatedSubsetSums.Weighted
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- A zero-based finite ranking and its totalized real score lookup.
Only values at ranks strictly below n are specified. -/
structure SortedScoreModel {X : Type*} (score : X → ℝ) (n : ℕ) where
  rank : X ≃ Fin n
  value : ℕ → ℝ
  lookup : ∀ x, value (rank x).val = score x
  increasing : StrictMono (fun i : Fin n => value i.val)
  gap : ∀ i : ℕ, i + 1 < n → 1 ≤ value (i + 1) - value i

/-- Sorting any finite unit-separated real score set establishes a rank
equivalence, monotone score enumeration, and adjacent unit gaps. -/
noncomputable def sortedScoreModel {X : Type*} [Fintype X] {n : ℕ}
    (score : X → ℝ) (card : Fintype.card X = n)
    (sep : ∀ x y, x ≠ y → 1 ≤ |score x - score y|) :
    SortedScoreModel score n := by
  classical
  have si : Function.Injective score := by
    intro x y h
    by_contra ne
    have hz := sep x y ne
    rw [h, sub_self, abs_zero] at hz
    exact (not_le_of_gt zero_lt_one) hz
  let S : Finset ℝ := Finset.univ.image score
  have cS : S.card = n := by
    change (Finset.univ.image score).card = n
    rw [Finset.card_image_of_injective _ si, Finset.card_univ, card]
  let toS (x : X) : S :=
    ⟨score x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  have bi : Function.Bijective toS := by
    constructor
    · intro x y h
      exact si (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, _, h⟩ := Finset.mem_image.mp y.prop
      exact ⟨x, Subtype.ext h⟩
  let e : X ≃ S := Equiv.ofBijective toS bi
  let ord : Fin n ≃o S := S.orderIsoOfFin cS
  let r : X ≃ Fin n := e.trans ord.symm.toEquiv
  let v (i : ℕ) : ℝ := if h : i < n then (ord ⟨i,h⟩ : ℝ) else 0
  have atFin (i : Fin n) : v i.val = (ord i : ℝ) := by
    simp [v, i.isLt]
  have lookup (x : X) : v (r x).val = score x := by
    rw [atFin]
    change (ord (ord.symm (e x)) : ℝ) = score x
    rw [ord.apply_symm_apply]
    rfl
  have inc : StrictMono (fun i : Fin n => v i.val) := by
    intro i j hij
    simp only [atFin]
    exact ord.strictMono hij
  have gap : ∀ i : ℕ, i + 1 < n → 1 ≤ v (i+1) - v i := by
    intro i hi
    let u : Fin n := ⟨i, by omega⟩
    let z : Fin n := ⟨i+1, hi⟩
    have ilt : u < z := Nat.lt_succ_self i
    have h := sep (r.symm z) (r.symm u) (fun h => (ne_of_gt ilt) (r.symm.injective h))
    rw [← lookup (r.symm z), ← lookup (r.symm u)] at h
    simp only [Equiv.apply_symm_apply] at h
    rw [abs_of_pos (sub_pos.mpr (inc ilt))] at h
    exact h
  exact ⟨r,v,lookup,inc,gap⟩

noncomputable def weightedCubeRankModel (w : Fin 9 → ℝ)
    (sep : ∀ x y : Cube 9, x ≠ y → 1 ≤ |weighted 9 w x - weighted 9 w y|) :
    SortedScoreModel (weighted 9 w) 512 :=
  sortedScoreModel (weighted 9 w) (cube_card 9) sep

noncomputable def weightedFinsetRankModel (w : Fin 9 → ℝ)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    SortedScoreModel (fun A : Finset (Fin 9) => ∑ i ∈ A, w i) 512 :=
  sortedScoreModel _ (by simp [Fintype.card_finset]) sep

/-- Existential interface matching the cube cut and critical-score lemmas. -/
theorem exists_weighted_rank_model (w : Fin 9 → ℝ)
    (sep : ∀ x y : Cube 9, x ≠ y → 1 ≤ |weighted 9 w x - weighted 9 w y|) :
    ∃ (r : Cube 9 ≃ Fin 512) (v : ℕ → ℝ),
      (∀ x, v (r x).val = weighted 9 w x) ∧
      StrictMono (fun i : Fin 512 => v i.val) ∧
      ∀ i : ℕ, i + 1 < 512 → 1 ≤ v (i + 1) - v i := by
  let m := weightedCubeRankModel w sep
  exact ⟨m.rank, m.value, m.lookup, m.increasing, m.gap⟩

#print axioms sortedScoreModel
#print axioms weightedFinsetRankModel
#print axioms exists_weighted_rank_model

end NineSeparatedSubsetSums
