module

public import Mathlib.Basic.Real.Basic
public import NineSeparatedSubsetSums.ConwayGuyNineNat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- The Conway–Guy configuration viewed as real weights. -/
noncomputable def conwayGuyNine (i : Fin 9) : ℝ := (conwayGuyNineNat i : ℝ)

private theorem cast_sum_real (A : Finset (Fin 9)) :
    ((∑ i ∈ A, conwayGuyNineNat i : ℕ) : ℝ) = ∑ i ∈ A, (conwayGuyNineNat i : ℝ) := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih => simp only [Finset.sum_insert ha, Nat.cast_add, ih]

private theorem cast_gap {a b : ℕ} (lt : a < b) : (1 : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
  apply le_sub_iff_add_le.mpr
  have h : ((1 + a : ℕ) : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr <|
    by simpa only [Nat.add_comm] using Nat.succ_le_of_lt lt
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem conwayGuyNine_separated (A B : Finset (Fin 9)) (ne : A ≠ B) :
    1 ≤ |(∑ i ∈ A, conwayGuyNine i) - (∑ i ∈ B, conwayGuyNine i)| := by
  have hn : (∑ i ∈ A, conwayGuyNineNat i) ≠ (∑ i ∈ B, conwayGuyNineNat i) :=
    fun h => ne (conwayGuyNineNat_injective h)
  simp only [conwayGuyNine, ← cast_sum_real]
  rcases lt_or_gt_of_ne hn with h | h
  · rw [abs_sub_comm]
    exact (cast_gap h).trans (le_abs_self _)
  · exact (cast_gap h).trans (le_abs_self _)

theorem conwayGuyNine_pos (i : Fin 9) : 0 < conwayGuyNine i := by
  apply Nat.cast_pos.mpr
  exact conwayGuyNineNat_pos i

theorem conwayGuyNine_le (i : Fin 9) : conwayGuyNine i ≤ 161 := by
  change (conwayGuyNineNat i : ℝ) ≤ ((161 : ℕ) : ℝ)
  apply Nat.cast_le.mpr
  exact conwayGuyNineNat_le i

theorem conwayGuyNine_attains : conwayGuyNine (8 : Fin 9) = 161 := by
  exact congrArg (fun n : ℕ => (n : ℝ)) conwayGuyNineNat_attains

/-- The real nine-weight problem has a witness with largest weight exactly 161. -/
theorem separated_nine_upper_161 :
    ∃ w : Fin 9 → ℝ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ 161) ∧ (∃ i, w i = 161) ∧
      ∀ A B : Finset (Fin 9), A ≠ B →
        1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)| :=
  ⟨conwayGuyNine, conwayGuyNine_pos, conwayGuyNine_le, ⟨8, conwayGuyNine_attains⟩,
    conwayGuyNine_separated⟩

#print axioms separated_nine_upper_161

end NineSeparatedSubsetSums
