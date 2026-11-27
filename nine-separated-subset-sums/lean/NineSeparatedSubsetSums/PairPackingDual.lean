import NineSeparatedSubsetSums.SignedMoment
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- Feasible half of the alternating dual potential on residues mod 592. -/
def pairHalfPotential (r : ℤ) : ℤ :=
  max 0 (min 417600 (min ((592-r)^2) (417600-(296-r)^2)))

def pairPotential (z : ℤ) : ℤ :=
  let r := z % 592
  if r < 296 then pairHalfPotential r else 417600 - pairHalfPotential (r-296)

private theorem pairHalfPotential_bounds (r : ℤ) :
    0 ≤ pairHalfPotential r ∧ pairHalfPotential r ≤ 417600 := by
  constructor
  · exact le_max_left _ _
  · apply max_le_iff.mpr
    exact ⟨by decide, min_le_left _ _⟩

theorem pairPotential_bounds (z : ℤ) :
    0 ≤ pairPotential z ∧ pairPotential z ≤ 417600 := by
  by_cases h : z % 592 < 296
  · simpa [pairPotential, h] using pairHalfPotential_bounds (z % 592)
  · have hB := pairHalfPotential_bounds (z%592-296)
    simp only [pairPotential, if_neg h]
    omega

theorem pairPotential_add296 (z : ℤ) :
    pairPotential z + pairPotential (z+296) = 417600 := by
  have h₀ : 0 ≤ z % 592 := Int.emod_nonneg _ (by decide)
  have h₁ : z % 592 < 592 := Int.emod_lt_of_pos _ (by decide)
  by_cases h : z % 592 < 296
  · have e : (z+296) % 592 = z % 592 + 296 := by omega
    have h' : ¬ z % 592 + 296 < 296 := by omega
    simp [pairPotential, h, e, h']
  · have e : (z+296) % 592 = z % 592 - 296 := by omega
    have h' : z % 592 - 296 < 296 := by omega
    simp [pairPotential, h, e, h']

def pairNegCost (z : ℤ) : ℤ := min 0 (z^2 - pairPotential z)

private theorem pairNegCost_eq_zero (z : ℤ)
    (outer : z < -646 ∨ 646 < z) : pairNegCost z = 0 := by
  have above : 417600 ≤ z^2 := by
    rcases outer with h | h
    · have k := mul_nonneg (show 0 ≤ -z-647 by omega) (show 0 ≤ -z+647 by omega)
      nlinarith only [k]
    · have k := mul_nonneg (show 0 ≤ z-647 by omega) (show 0 ≤ z+647 by omega)
      nlinarith only [k]
  have h := (pairPotential_bounds z).2
  unfold pairNegCost
  exact min_eq_left (by omega)

def pairParityBox (p : ℤ) : Finset ℤ :=
  (Finset.Icc (-646) 646).filter (fun z => z % 2 = p)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem pairParityBox_even :
    (∑ z ∈ pairParityBox 0, pairNegCost z) = -54839296 := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem pairParityBox_odd :
    (∑ z ∈ pairParityBox 1, pairNegCost z) = -54839808 := by decide +kernel

theorem pairNegCost_sum_lower (S : Finset ℤ) (p : ℤ)
    (hp : p = 0 ∨ p = 1) (parity : ∀ z ∈ S, z%2 = p) :
    -54839808 ≤ ∑ z ∈ S, pairNegCost z := by
  let T := S.filter (fun z => z ∈ pairParityBox p)
  have same : (∑ z ∈ T, pairNegCost z) = ∑ z ∈ S, pairNegCost z := by
    change (∑ z ∈ S.filter (fun z => z ∈ pairParityBox p), pairNegCost z) = _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hzB : z ∈ pairParityBox p
    · simp [hzB]
    · have out : z < -646 ∨ 646 < z := by
        by_contra! h
        apply hzB
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr h,parity z hz⟩
      simp [hzB, pairNegCost_eq_zero z out]
  have sub : T ⊆ pairParityBox p := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hneg := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun z => -pairNegCost z) sub (fun z _ _ =>
      neg_nonneg.mpr (min_le_left _ _))
  simp only [Finset.sum_neg_distrib] at hneg
  have hbox : -54839808 ≤ ∑ z ∈ pairParityBox p, pairNegCost z := by
    rcases hp with rfl | rfl
    · rw [pairParityBox_even]
      decide
    · rw [pairParityBox_odd]
  omega

theorem pairPotential_spread (scores : List ℤ) :
    ((spread 148 scores).map pairPotential).sum = 417600*(scores.length : ℤ) := by
  induction scores with
  | nil => simp [spread]
  | cons z scores ih =>
    have step := pairPotential_add296 (z-148)
    have e : z-148+296 = z+148 := by omega
    rw [e] at step
    simp only [spread, List.flatMap_cons, List.cons_append, List.nil_append,
      List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at *
    rw [ih]
    linarith

/-- Squared-score lower bound for 256 disjoint pairs separated by 296
on a common parity lattice. No rank or Harper premise is required. -/
theorem pairPackingSquareLower (scores : List ℤ) (len : scores.length = 256)
    (distinct : (spread 148 scores).Nodup) (p : ℤ) (hp : p = 0 ∨ p = 1)
    (parity : ∀ z ∈ spread 148 scores, z%2 = p) :
    52065792 ≤ ((spread 148 scores).map (· ^ 2)).sum := by
  let S := (spread 148 scores).toFinset
  have pa := pairNegCost_sum_lower S p hp (fun z hz => parity z (List.mem_toFinset.mp hz))
  have point : ∀ z ∈ S, pairPotential z + pairNegCost z ≤ z^2 := by
    intro z _
    have h := min_le_right (0 : ℤ) (z^2 - pairPotential z)
    change pairNegCost z ≤ z^2 - pairPotential z at h
    omega
  have total := Finset.sum_le_sum point
  rw [Finset.sum_add_distrib] at total
  change (∑ z ∈ (spread 148 scores).toFinset, pairPotential z)
    + (∑ z ∈ S, pairNegCost z) ≤
      ∑ z ∈ (spread 148 scores).toFinset, z^2 at total
  rw [List.sum_toFinset pairPotential distinct, List.sum_toFinset (· ^ 2) distinct,
    pairPotential_spread, len] at total
  omega

#print axioms pairPotential_add296
#print axioms pairParityBox_even
#print axioms pairParityBox_odd
#print axioms pairPackingSquareLower

end NineSeparatedSubsetSums
