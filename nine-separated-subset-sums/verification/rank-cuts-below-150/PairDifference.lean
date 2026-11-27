import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Option

open scoped BigOperators

namespace NineGap

def Separated {α : Type*} (w : α → ℝ) : Prop :=
  ∀ A B : Finset α, A ≠ B →
    1 ≤ |(∑ a ∈ A, w a) - (∑ b ∈ B, w b)|

/-- Keep the ordinary indices; replace the two distinguished coordinates
    `none` and `some none` by their signed difference. -/
def replacePair {α : Type*} (w : Option (Option α) → ℝ) : Option α → ℝ
  | none => w (some none) - w none
  | some i => w (some (some i))

def optEmb (α : Type*) : Option α ↪ Option (Option α) :=
  ⟨some, Option.some_injective _⟩

def liftSubset {α : Type*} [DecidableEq α] (A : Finset (Option α)) :
    Finset (Option (Option α)) :=
  insert (if none ∈ A then some none else none) ((A.erase none).map (optEmb α))

theorem liftSubset_injective {α : Type*} [DecidableEq α] :
    Function.Injective (liftSubset (α := α)) := by
  intro A B h
  ext a
  cases a with
  | none =>
    have hh := congrArg (fun s : Finset (Option (Option α)) => some none ∈ s) h
    by_cases ha : none ∈ A <;> by_cases hb : none ∈ B <;>
      simp [liftSubset, optEmb, ha, hb] at hh ⊢
  | some i =>
    have hh := congrArg (fun s : Finset (Option (Option α)) => some (some i) ∈ s) h
    by_cases ha : none ∈ A <;> by_cases hb : none ∈ B <;>
      simpa [liftSubset, optEmb, ha, hb] using hh

theorem liftSubset_sum {α : Type*} [DecidableEq α]
    (w : Option (Option α) → ℝ) (A : Finset (Option α)) :
    (∑ a ∈ liftSubset A, w a) = (∑ a ∈ A, replacePair w a) + w none := by
  have he : ∑ a ∈ A.erase none, w (some a) = ∑ a ∈ A.erase none, replacePair w a := by
    apply Finset.sum_congr rfl
    intro i hi
    cases i with
    | none => simp at hi
    | some i => rfl
  by_cases h : none ∈ A
  · have hh : some none ∉ (A.erase none).map (optEmb α) := by simp [optEmb]
    rw [liftSubset, ite_eq_left h, Finset.sum_insert hh, Finset.sum_map]
    change w (some none) + (∑ a ∈ A.erase none, w (some a)) = _
    rw [he, ← Finset.sum_erase_add A (replacePair w) h]
    simp only [replacePair]
    rw [add_assoc, sub_add_cancel, add_comm]
  · have hh : (none : Option (Option α)) ∉ (A.erase none).map (optEmb α) := by simp [optEmb]
    rw [liftSubset, ite_eq_right h, Finset.sum_insert hh, Finset.sum_map]
    change w none + (∑ a ∈ A.erase none, w (some a)) = _
    rw [he, Finset.erase_eq_of_notMem h, add_comm]

theorem separated_replacePair {α : Type*} [DecidableEq α]
    (w : Option (Option α) → ℝ) (h : Separated w) :
    Separated (replacePair w) := by
  intro A B hAB
  have H := h (liftSubset A) (liftSubset B) (fun h' => hAB (liftSubset_injective h'))
  rw [liftSubset_sum, liftSubset_sum, add_sub_add_right_eq_sub] at H
  exact H

#print axioms separated_replacePair

end NineGap
