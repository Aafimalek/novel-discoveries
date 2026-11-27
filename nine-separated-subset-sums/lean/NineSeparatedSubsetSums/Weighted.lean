import NineSeparatedSubsetSums.Cube
import Mathlib.Basic.Real.Basic

namespace NineSeparatedSubsetSums

def weighted : (n : ℕ) → (Fin n → ℝ) → Cube n → ℝ
  | 0, _, _ => 0
  | n + 1, w, (x, b) =>
      weighted n (fun j => w j.castSucc) x + if b then w (Fin.last n) else 0

theorem near_weighted_bound (n : ℕ) (w : Fin n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hw : ∀ i, |w i| ≤ M) (x y : Cube n) (h : near n x y) :
    |weighted n w x - weighted n w y| ≤ M := by
  induction n with
  | zero => simpa [weighted] using hM
  | succ d ih =>
      change Cube d × Bool at x y
      obtain ⟨x, a⟩ := x
      obtain ⟨y, b⟩ := y
      change (a = b ∧ near d x y) ∨ x = y at h
      rcases h with ⟨rfl, hxy⟩ | rfl
      · simpa only [weighted, add_sub_add_right_eq_sub] using
          ih (fun j : Fin d => w j.castSucc) (fun j => hw j.castSucc) x y hxy
      · cases a <;> cases b <;>
          simp [weighted, hM, hw (Fin.last d), sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

theorem accumulate_gaps (v : ℕ → ℝ) (bound : ℕ)
    (hgap : ∀ i : ℕ, i + 1 < bound → 1 ≤ v (i + 1) - v i)
    (i k : ℕ) (hik : i + k < bound) :
    (k : ℝ) ≤ v (i + k) - v i := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h₁ := ih (by omega)
      have h₂ := hgap (i + k) (by omega)
      rw [Nat.cast_succ]
      have hsum : (k : ℝ) + 1 ≤ v (i + k + 1) - v i := by linarith [h₁, h₂]
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hsum

#print axioms near_weighted_bound
#print axioms accumulate_gaps

end NineSeparatedSubsetSums

