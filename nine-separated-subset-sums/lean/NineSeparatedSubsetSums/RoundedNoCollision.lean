import NineSeparatedSubsetSums.CenterCollision
import Mathlib.Data.Finset.SDiff

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- If the central interval has the indicated endpoints and its rounded
sum is injective there, then rounding is injective everywhere. -/
theorem roundedInjective_of_center {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℤ) (x : ι → ℝ) (a b : ℝ)
    (hW : ∀ i, 0 ≤ w i ∧ w i ≤ 148)
    (hX : ∀ A : Finset ι, 0 ≤ (∑ i ∈ A, x i) - ((∑ i ∈ A, w i : ℤ) : ℝ) ∧
      (∑ i ∈ A, x i) - ((∑ i ∈ A, w i : ℤ) : ℝ) < 9)
    (ha : 0 ≤ a - ((∑ i, w i : ℤ) : ℝ) / 2 + 197 / 2 ∧
      a - ((∑ i, w i : ℤ) : ℝ) / 2 + 197 / 2 < 9)
    (hb : 0 ≤ b - ((∑ i, w i : ℤ) : ℝ) / 2 - 197 / 2 ∧
      b - ((∑ i, w i : ℤ) : ℝ) / 2 - 197 / 2 < 9)
    (hinj : Set.InjOn (fun A : Finset ι => ∑ i ∈ A, w i)
      {A | a < (∑ i ∈ A, x i) ∧ (∑ i ∈ A, x i) < b}) :
    Function.Injective (fun A : Finset ι => ∑ i ∈ A, w i) := by
  intro A B hAB
  let S := A \ B
  let T := B \ A
  let I := A ∩ B
  have hsI : Disjoint S I := Finset.disjoint_left.mpr fun i hs hi =>
    (Finset.mem_sdiff.mp hs).2 (Finset.mem_inter.mp hi).2
  have htI : Disjoint T I := Finset.disjoint_left.mpr fun i ht hi =>
    (Finset.mem_sdiff.mp ht).2 (Finset.mem_inter.mp hi).1
  have hst : Disjoint S T := Finset.disjoint_left.mpr fun i hs ht =>
    (Finset.mem_sdiff.mp hs).2 (Finset.mem_sdiff.mp ht).1
  have hsU : S ∪ I = A := by
    ext i
    simp only [S, I, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have htU : T ∪ I = B := by
    ext i
    simp only [T, I, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have heq : (∑ i ∈ S, w i) = ∑ i ∈ T, w i := by
    change (∑ i ∈ A, w i) = ∑ i ∈ B, w i at hAB
    rw [← hsU, ← htU, Finset.sum_union hsI, Finset.sum_union htI] at hAB
    omega
  obtain ⟨V, hSV, hTV, he, hS1, hS2, hT1, hT2⟩ :=
    centerCollision w x S T hst heq hW hX a b ha hb
  have h := hinj (show S ∪ V ∈ _ from ⟨hS1, hS2⟩)
    (show T ∪ V ∈ _ from ⟨hT1, hT2⟩) he
  have hc : S = T := by
    ext i
    constructor
    · intro hi
      have hu : i ∈ T ∪ V := h ▸ Finset.mem_union_left V hi
      exact (Finset.mem_union.mp hu).resolve_right (fun hv => Finset.disjoint_left.mp hSV hi hv)
    · intro hi
      have hu : i ∈ S ∪ V := h.symm ▸ Finset.mem_union_left V hi
      exact (Finset.mem_union.mp hu).resolve_right (fun hv => Finset.disjoint_left.mp hTV hi hv)
  rw [← hsU, ← htU, hc]

#print axioms roundedInjective_of_center

end NineSeparatedSubsetSums
