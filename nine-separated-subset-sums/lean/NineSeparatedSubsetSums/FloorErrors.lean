import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace NineSeparatedSubsetSums

theorem rounded_weight_bounds (x : ℝ) (h1 : 1 ≤ x) (h149 : x < 149) :
    1 ≤ ⌊x⌋ ∧ ⌊x⌋ ≤ 148 := by
  constructor
  · exact Int.le_floor.mpr (by simpa using h1)
  · have h : ⌊x⌋ < 149 := Int.floor_lt.mpr (by simpa using h149)
    omega

theorem rounded_subset_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι ≤ 9) (w : ι → ℝ) (δ : ℝ) (hδ : 0 ≤ δ ∧ δ < 1)
    (hf : ∀ i, Int.fract (w i) ≤ δ) (S : Finset ι) :
    0 ≤ (∑ i ∈ S, w i) - ((∑ i ∈ S, ⌊w i⌋ : ℤ) : ℝ) ∧
      (∑ i ∈ S, w i) - ((∑ i ∈ S, ⌊w i⌋ : ℤ) : ℝ) < 9 := by
  have hc : S.card ≤ 9 := (Finset.card_le_univ _).trans hcard
  have hcast : (S.card : ℝ) ≤ 9 := by exact_mod_cast hc
  push_cast
  rw [← Finset.sum_sub_distrib]
  change 0 ≤ ∑ i ∈ S, Int.fract (w i) ∧ (∑ i ∈ S, Int.fract (w i)) < 9
  constructor
  · exact Finset.sum_nonneg (fun i _ => Int.fract_nonneg (w i))
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ S) => hf i)
    rw [Finset.sum_const, nsmul_eq_mul] at h
    have hh := mul_le_mul_of_nonneg_right hcast hδ.1
    linarith [hδ.2]

#print axioms rounded_weight_bounds
#print axioms rounded_subset_error

end NineSeparatedSubsetSums
