import NineSeparatedSubsetSums.FloorErrors
import NineSeparatedSubsetSums.RoundedNoCollision
import NineSeparatedSubsetSums.RankReflection
import NineSeparatedSubsetSums.ComplementRanks

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- Offset constancy in the first block suffices to prove injectivity of all
rounded sums: reflect the block, then translate any candidate collision. -/
theorem rounded_injective_from_first_block
    (w : Fin 9 → ℝ) (r : Finset (Fin 9) ≃ Fin 512) (v : ℕ → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ ∧ δ < 1)
    (hw : ∀ i, 1 ≤ w i ∧ w i < 149)
    (hf : ∀ i, Int.fract (w i) ≤ δ)
    (inc : StrictMono (fun j : Fin 512 => v j.val))
    (lookup : ∀ S, v (r S).val = ∑ i ∈ S, w i)
    (K : ℤ) (first : ∀ S, 157 ≤ (r S).val → (r S).val ≤ 305 →
      ((r S).val : ℤ) - (∑ i ∈ S, ⌊w i⌋) = K) :
    Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, ⌊w i⌋) := by
  classical
  let a (j : ℕ) : ℤ := ∑ i ∈ r.symm (Fin.ofNat 512 j), ⌊w i⌋
  let T : ℤ := ∑ i : Fin 9, ⌊w i⌋
  have aRank (S : Finset (Fin 9)) : a (r S).val = ∑ i ∈ S, ⌊w i⌋ := by
    have ee : Fin.ofNat 512 (r S).val = r S := by
      exact Fin.ofNat_val_eq_self (r S)
    simp only [a, ee, Equiv.symm_apply_apply]
  have rev (S : Finset (Fin 9)) : r Sᶜ = Fin.rev (r S) := by
    refine rank_reflect_of_score r (fun j : Fin 512 => v j.val) inc (·ᶜ) (∑ i, w i) ?_ S
    intro A
    simp only [lookup]
    have h := Finset.sum_compl_add_sum A w
    linarith
  have cEq (j : ℕ) (hj : j ≤ 511) : a (511 - j) = T - a j := by
    let J : Fin 512 := ⟨j, by omega⟩
    let S := r.symm J
    have e : (r S).val = j := by simp [S, J]
    have er : (r Sᶜ).val = 511 - j := by
      rw [rev, Fin.val_rev, e]
      omega
    have eh := aRank S
    rw [e] at eh
    rw [eh, ← er, aRank]
    have h := Finset.sum_compl_add_sum S (fun i => ⌊w i⌋)
    dsimp [T]
    omega
  have fEq (j : ℕ) (hj : 157 ≤ j) (hj' : j ≤ 305) : (j : ℤ) - a j = K := by
    let J : Fin 512 := ⟨j, by omega⟩
    let S := r.symm J
    have e : (r S).val = j := by simp [S, J]
    have hh := first S (by omega) (by omega)
    rw [← aRank S, e] at hh
    exact hh
  obtain ⟨central, lo, hi⟩ := complement_ranks_extend_offset a T K cEq fEq
  have errors (S : Finset (Fin 9)) :=
    rounded_subset_error (by decide : Fintype.card (Fin 9) ≤ 9) w δ hδ hf S
  have errorRank (j : Fin 512) :
      0 ≤ v j.val - (a j.val : ℝ) ∧ v j.val - (a j.val : ℝ) < 9 := by
    let S := r.symm j
    have e : r S = j := r.apply_symm_apply j
    have e1 := lookup S
    have e2 := aRank S
    rw [e] at e1 e2
    rw [e1, e2]
    exact errors S
  have elo := errorRank 157
  have ehi := errorRank 354
  change 0 ≤ v 157 - (a 157 : ℝ) ∧ v 157 - (a 157 : ℝ) < 9 at elo
  change 0 ≤ v 354 - (a 354 : ℝ) ∧ v 354 - (a 354 : ℝ) < 9 at ehi
  have lor : 2 * (a 157 : ℝ) = (T : ℝ) - 197 := by exact_mod_cast lo
  have hir : 2 * (a 354 : ℝ) = (T : ℝ) + 197 := by exact_mod_cast hi
  refine roundedInjective_of_center (fun i => ⌊w i⌋) w (v 157) (v 354)
    (fun i => ⟨(by have x := rounded_weight_bounds (w i) (hw i).1 (hw i).2; omega),
      (rounded_weight_bounds (w i) (hw i).1 (hw i).2).2⟩)
    errors ?_ ?_ ?_
  · change 0 ≤ v 157 - (T : ℝ) / 2 + 197 / 2 ∧ v 157 - (T : ℝ) / 2 + 197 / 2 < 9
    constructor <;> linarith [elo.1, elo.2]
  · change 0 ≤ v 354 - (T : ℝ) / 2 - 197 / 2 ∧ v 354 - (T : ℝ) / 2 - 197 / 2 < 9
    constructor <;> linarith [ehi.1, ehi.2]
  · intro S hS U hU e
    have range (A : Finset (Fin 9))
        (hA : v 157 < (∑ i ∈ A, w i) ∧ (∑ i ∈ A, w i) < v 354) :
        157 ≤ (r A).val ∧ (r A).val ≤ 354 := by
      rw [← lookup] at hA
      have h1 : (157 : Fin 512) < r A := inc.lt_iff_lt.mp hA.1
      have h2 : r A < (354 : Fin 512) := inc.lt_iff_lt.mp hA.2
      exact ⟨h1.le, h2.le⟩
    have s := range S hS
    have u := range U hU
    have cs := central _ s.1 s.2
    have cu := central _ u.1 u.2
    change (∑ i ∈ S, ⌊w i⌋) = ∑ i ∈ U, ⌊w i⌋ at e
    rw [aRank] at cs cu
    exact r.injective (Fin.ext (by omega))

#print axioms rounded_injective_from_first_block

end NineSeparatedSubsetSums
