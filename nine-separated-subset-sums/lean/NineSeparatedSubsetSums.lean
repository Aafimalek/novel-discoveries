import Mathlib
import NineSeparatedSubsetSums.GapBlock
import NineSeparatedSubsetSums.FractionReflect
import NineSeparatedSubsetSums.CriticalEdge
import NineSeparatedSubsetSums.PackingMoment
import NineSeparatedSubsetSums.SignedMoment
import NineSeparatedSubsetSums.LowShelf
import NineSeparatedSubsetSums.Weighted
import NineSeparatedSubsetSums.SlabWalk
import NineSeparatedSubsetSums.CenterPrefix
import NineSeparatedSubsetSums.RankCut

open scoped BigOperators

namespace NineSeparatedSubsetSums

variable {ι : Type*} [DecidableEq ι]

/-- The fractional errors on a set of at most six coordinates add to less than one. -/
theorem sumError_lt_one (S : Finset ι) (e : ι → ℝ) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ : 6 * δ < 1)
    (hcap : S.card ≤ 6) (he : ∀ i ∈ S, 0 ≤ e i ∧ e i ≤ δ) :
    0 ≤ (∑ i ∈ S, e i) ∧ (∑ i ∈ S, e i) < 1 := by
  refine ⟨Finset.sum_nonneg (fun i hi => (he i hi).1), ?_⟩
  have h₁ : (∑ i ∈ S, e i) ≤ ∑ _i ∈ S, δ :=
    Finset.sum_le_sum (fun i hi => (he i hi).2)
  rw [Finset.sum_const, nsmul_eq_mul] at h₁
  have hc : (S.card : ℝ) ≤ 6 := by exact_mod_cast hcap
  exact lt_of_le_of_lt (h₁.trans (mul_le_mul_of_nonneg_right hc hδ₀)) hδ

/-- The proven rounding reduction in the paper, with the fractional-part and
collision-cardinality estimates supplied as hypotheses. This does not assert
those estimates or prove the paper's numerical bound. -/
theorem rounding_injective (x : ι → ℝ) (a : ι → ℤ) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ : 6 * δ < 1)
    (he : ∀ i, 0 ≤ x i - (a i : ℝ) ∧ x i - (a i : ℝ) ≤ δ)
    (hsep : ∀ S T : Finset ι, S ≠ T →
      1 ≤ |(∑ i ∈ S, x i) - ∑ i ∈ T, x i|)
    (hcap : ∀ S T : Finset ι, Disjoint S T → S ≠ T →
      (∑ i ∈ S, a i) = (∑ i ∈ T, a i) → S.card ≤ 6 ∧ T.card ≤ 6) :
    Function.Injective (fun S : Finset ι => ∑ i ∈ S, a i) := by
  classical
  intro A B hAB
  by_contra hne
  let S := A \ B
  let T := B \ A
  let I := A ∩ B
  change (∑ i ∈ A, a i) = (∑ i ∈ B, a i) at hAB
  have hsI : Disjoint S I := by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hj).2
  have htI : Disjoint T I := by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hj).1
  have hst : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hsU : S ∪ I = A := by
    ext i
    simp only [S, I, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have htU : T ∪ I = B := by
    ext i
    simp only [T, I, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hneST : S ≠ T := by
    intro heq
    apply hne
    rw [← hsU, ← htU, heq]
  have hs_sum : (∑ i ∈ A, a i) = (∑ i ∈ S, a i) + ∑ i ∈ I, a i := by
    rw [← hsU, Finset.sum_union hsI]
  have ht_sum : (∑ i ∈ B, a i) = (∑ i ∈ T, a i) + ∑ i ∈ I, a i := by
    rw [← htU, Finset.sum_union htI]
  have hround : (∑ i ∈ S, a i) = (∑ i ∈ T, a i) := by
    linarith
  obtain ⟨hs, ht⟩ := hcap S T hst hneST hround
  have hS := sumError_lt_one S (fun i => x i - (a i : ℝ)) δ hδ₀ hδ hs (fun i _ => he i)
  have hT := sumError_lt_one T (fun i => x i - (a i : ℝ)) δ hδ₀ hδ ht (fun i _ => he i)
  simp only [Finset.sum_sub_distrib] at hS hT
  have hcast : (∑ i ∈ S, (a i : ℝ)) = ∑ i ∈ T, (a i : ℝ) := by
    exact_mod_cast hround
  have hd : |(∑ i ∈ S, x i) - ∑ i ∈ T, x i| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [hS.1, hS.2, hT.1, hT.2]
  exact (not_lt_of_ge (hsep S T hneST)) hd

#print axioms rounding_injective

end NineSeparatedSubsetSums
