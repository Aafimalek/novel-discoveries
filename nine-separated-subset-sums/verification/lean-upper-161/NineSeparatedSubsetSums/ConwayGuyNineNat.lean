module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Init.Data.Nat.Bitwise.Lemmas
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- The nine-element Conway–Guy configuration in Borwein–Mossinghoff, Table 5. -/
def conwayGuyNineNat (i : Fin 9) : ℕ :=
  [77, 117, 137, 148, 154, 157, 159, 160, 161][i.val]!

private def allSubsets : List (List (Fin 9)) := (List.finRange 9).sublists

private def rep (a : Finset (Fin 9)) : List (Fin 9) :=
  (List.finRange 9).filter (fun i => decide (i ∈ a))

private theorem rep_mem (a : Finset (Fin 9)) : rep a ∈ allSubsets :=
  List.mem_sublists.mpr List.filter_sublist

private theorem rep_nodup (a : Finset (Fin 9)) : (rep a).Nodup :=
  (List.nodup_finRange 9).sublist List.filter_sublist

private theorem rep_toFinset (a : Finset (Fin 9)) : (rep a).toFinset = a := by
  ext i
  simp [rep, List.mem_finRange]

private def score (l : List (Fin 9)) : Nat := (l.map conwayGuyNineNat).sum

private theorem score_rep (a : Finset (Fin 9)) : score (rep a) = ∑ i ∈ a, conwayGuyNineNat i := by
  calc
    score (rep a) = ∑ i ∈ (rep a).toFinset, conwayGuyNineNat i :=
      (List.sum_toFinset conwayGuyNineNat (rep_nodup a)).symm
    _ = _ := by rw [rep_toFinset]

private def sums : List Nat := allSubsets.map score

/-- Check the 512 scores in one pass, using one bit per possible sum. -/
private def distinctMask : List Nat → Option Nat
  | [] => some 0
  | a :: l =>
    match distinctMask l with
    | none => none
    | some m => if m.testBit a then none else some (m ||| 2^a)

private theorem distinctMask_sound (l : List Nat) (m : Nat) (h : distinctMask l = some m) :
    l.Nodup ∧ ∀ b, m.testBit b = true ↔ b ∈ l := by
  induction l generalizing m with
  | nil =>
    have hm : m = 0 := by simpa [distinctMask, eq_comm] using h
    subst m
    simp
  | cons a t ih =>
    cases e : distinctMask t with
    | none => simp [distinctMask, e] at h
    | some n =>
      rcases ih n e with ⟨ht, hm⟩
      by_cases ha : n.testBit a = true
      · simp [distinctMask, e, ha] at h
      · simp [distinctMask, e, ha] at h
        subst m
        constructor
        · exact List.nodup_cons.mpr ⟨fun hx => ha ((hm a).mpr hx), ht⟩
        · intro b
          rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, hm b,
            decide_eq_true_eq, List.mem_cons]
          exact ⟨fun h => h.elim Or.inr (fun e => Or.inl e.symm),
            fun h => h.elim (fun e => Or.inr e.symm) Or.inl⟩

set_option maxRecDepth 4000 in
private theorem sums_checked : (distinctMask sums).isSome = true := by decide +kernel

private theorem sums_nodup : sums.Nodup := by
  cases e : distinctMask sums with
  | none => have h := sums_checked; simp [e] at h
  | some m => exact (distinctMask_sound sums m e).1

private theorem inj_of_pairwise_mapped {α β : Type} (f : α → β) (l : List α)
    (h : l.Pairwise (fun x y => f x ≠ f y)) :
    ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b := by
  induction l with
  | nil => simp
  | cons x t ih =>
    intro a b ha hb eq
    have both := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with hax | hat
    · subst a
      rcases List.mem_cons.mp hb with hbx | hbt
      · subst b
        rfl
      · exact False.elim (both.1 _ hbt eq)
    · rcases List.mem_cons.mp hb with hbx | hbt
      · subst b
        exact False.elim (both.1 _ hat eq.symm)
      · exact ih both.2 hat hbt eq

theorem conwayGuyNineNat_injective :
    Function.Injective (fun a : Finset (Fin 9) => ∑ i ∈ a, conwayGuyNineNat i) := by
  intro a b eq
  have h := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp sums_nodup)
  have e : rep a = rep b :=
    inj_of_pairwise_mapped score allSubsets h (rep_mem a) (rep_mem b) <| by
      simpa only [score_rep] using eq
  simpa only [rep_toFinset] using congrArg List.toFinset e

theorem conwayGuyNineNat_pos (i : Fin 9) : 0 < conwayGuyNineNat i :=
  (show ∀ j, 0 < conwayGuyNineNat j by decide +kernel) i

theorem conwayGuyNineNat_le (i : Fin 9) : conwayGuyNineNat i ≤ 161 :=
  (show ∀ j, conwayGuyNineNat j ≤ 161 by decide +kernel) i

theorem conwayGuyNineNat_attains : conwayGuyNineNat (8 : Fin 9) = 161 := rfl

#print axioms conwayGuyNineNat_injective
end NineSeparatedSubsetSums
