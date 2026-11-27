import NineSeparatedSubsetSums.CenterFinset
import NineSeparatedSubsetSums.RoundedInterval
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- Equal rounded subset sums can be translated by the same disjoint subset
so that both exact sums are inside a central real interval. -/
theorem centerCollision {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℤ) (x : ι → ℝ) (S T : Finset ι)
    (hst : Disjoint S T) (hST : (∑ i ∈ S, w i) = ∑ i ∈ T, w i)
    (hW : ∀ i, 0 ≤ w i ∧ w i ≤ 148)
    (hX : ∀ A : Finset ι, 0 ≤ (∑ i ∈ A, x i) - ((∑ i ∈ A, w i : ℤ) : ℝ) ∧
      (∑ i ∈ A, x i) - ((∑ i ∈ A, w i : ℤ) : ℝ) < 9)
    (a b : ℝ)
    (ha : 0 ≤ a - ((∑ i, w i : ℤ) : ℝ) / 2 + 197 / 2 ∧
      a - ((∑ i, w i : ℤ) : ℝ) / 2 + 197 / 2 < 9)
    (hb : 0 ≤ b - ((∑ i, w i : ℤ) : ℝ) / 2 - 197 / 2 ∧
      b - ((∑ i, w i : ℤ) : ℝ) / 2 - 197 / 2 < 9) :
    ∃ V : Finset ι, Disjoint S V ∧ Disjoint T V ∧
      (∑ i ∈ S ∪ V, w i) = (∑ i ∈ T ∪ V, w i) ∧
      a < (∑ i ∈ S ∪ V, x i) ∧ (∑ i ∈ S ∪ V, x i) < b ∧
      a < (∑ i ∈ T ∪ V, x i) ∧ (∑ i ∈ T ∪ V, x i) < b := by
  let U := Finset.univ \ (S ∪ T)
  have hDU : Disjoint (S ∪ T) U := by
    exact Finset.disjoint_left.mpr (fun _ hi hu => (Finset.mem_sdiff.mp hu).2 hi)
  have hUnion : (S ∪ T) ∪ U = Finset.univ := by
    ext i
    simp [U]
  have htotal : (∑ i, w i) = 2 * (∑ i ∈ S, w i) + ∑ i ∈ U, w i := by
    rw [← hUnion, Finset.sum_union hDU, Finset.sum_union hst, ← hST]
    ring
  let t := ∑ i ∈ U, w i
  have ht : 0 ≤ t := Finset.sum_nonneg fun i _ => (hW i).1
  obtain ⟨V, hVU, hsmall, hlarge⟩ :=
    exists_subset_near_double_sum U w 148 t (by norm_num) ht (by dsimp [t]; omega)
      (fun i _ => hW i)
  have hDS : Disjoint S V := Finset.disjoint_left.mpr fun _ hi hv =>
    Finset.disjoint_left.mp hDU (Finset.mem_union_left T hi) (hVU hv)
  have hDT : Disjoint T V := Finset.disjoint_left.mpr fun _ hi hv =>
    Finset.disjoint_left.mp hDU (Finset.mem_union_right S hi) (hVU hv)
  have heq : (∑ i ∈ S ∪ V, w i) = ∑ i ∈ T ∪ V, w i := by
    rw [Finset.sum_union hDS, Finset.sum_union hDT, hST]
  let tot : ℝ := ((∑ i, w i : ℤ) : ℝ)
  let round : ℝ := ((∑ i ∈ S ∪ V, w i : ℤ) : ℝ)
  have hdoub : -148 ≤ 2 * (∑ i ∈ S ∪ V, w i) - ∑ i, w i ∧
      2 * (∑ i ∈ S ∪ V, w i) - ∑ i, w i ≤ 148 := by
    rw [Finset.sum_union hDS, htotal]
    dsimp [t] at hsmall hlarge
    constructor <;> omega
  have hdoubReal : -148 ≤ 2 * round - tot ∧ 2 * round - tot ≤ 148 := by
    dsimp [round, tot]
    constructor <;> exact_mod_cast (by first | exact hdoub.1 | exact hdoub.2)
  have hr : tot / 2 - 74 ≤ round ∧ round ≤ tot / 2 + 74 := by
    constructor <;> linarith [hdoubReal.1, hdoubReal.2]
  have ha' : 0 ≤ a - (tot / 2 - 197 / 2) ∧ a - (tot / 2 - 197 / 2) < 9 := by
    dsimp [tot]
    constructor <;> linarith [ha.1, ha.2]
  have hb' : 0 ≤ b - (tot / 2 + 197 / 2) ∧ b - (tot / 2 + 197 / 2) < 9 := by
    dsimp [tot]
    constructor <;> linarith [hb.1, hb.2]
  have hXS := hX (S ∪ V)
  have hXT := hX (T ∪ V)
  rw [← heq] at hXT
  have A := centered_inside_real (∑ i ∈ S ∪ V, x i) round _ _ tot rfl rfl hr hXS a b ha' hb'
  have B := centered_inside_real (∑ i ∈ T ∪ V, x i) round _ _ tot rfl rfl hr hXT a b ha' hb'
  exact ⟨V, hDS, hDT, heq, A.1, A.2, B.1, B.2⟩

#print axioms centerCollision

end NineSeparatedSubsetSums
