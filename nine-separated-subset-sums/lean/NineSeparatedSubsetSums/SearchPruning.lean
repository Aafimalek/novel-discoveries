import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

namespace NineSeparatedSubsetSums

/-- Largest possible remaining weight sum in a search branch with k
strictly decreasing positive weights bounded above by h. -/
def topSum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, h => h + topSum k (h - 1)

/-- Analogous square-sum bound; used by the exact enumeration. -/
def topSquare : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, h => h ^ 2 + topSquare k (h - 1)

theorem topSum_mono (k : ℕ) : Monotone (topSum k) := by
  induction k with
  | zero => intro _ _ _; exact le_rfl
  | succ k ih =>
    intro a b hab
    exact Nat.add_le_add hab (ih (by omega : a - 1 ≤ b - 1))

theorem topSquare_mono (k : ℕ) : Monotone (topSquare k) := by
  induction k with
  | zero => intro _ _ _; exact le_rfl
  | succ k ih =>
    intro a b hab
    exact Nat.add_le_add (Nat.pow_le_pow_left hab 2) (ih (by omega : a - 1 ≤ b - 1))

/-- Bounds used by the enumeration are valid for every descending tail,
not only for the candidate sequence that attains the bound. -/
theorem descending_weights_bounds (xs : List ℕ) (h : ℕ)
    (d : xs.Pairwise (· > ·)) (b : ∀ x ∈ xs, x ≤ h) :
    xs.sum ≤ topSum xs.length h ∧
      (xs.map (· ^ 2)).sum ≤ topSquare xs.length h := by
  induction xs generalizing h with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp d
    have b₁ : x ≤ h := b _ (by simp)
    have bs (y : ℕ) (hy : y ∈ xs) : y ≤ h - 1 := by have := hx y hy; omega
    obtain ⟨h1, h2⟩ := ih (h - 1) hxs bs
    constructor
    · simpa only [List.length_cons, List.sum_cons, topSum] using Nat.add_le_add b₁ h1
    · simpa only [List.length_cons, List.map_cons, List.sum_cons, topSquare] using
        Nat.add_le_add (Nat.pow_le_pow_left b₁ 2) h2

/-- A cut cannot reject any descending tail that achieves the required
total or square moment. This admits either capacity cut, as in the C++ code. -/
theorem capacity_cut_sound (xs : List ℕ) (h oldSum oldSq minSum minSq : ℕ)
    (d : xs.Pairwise (· > ·)) (b : ∀ x ∈ xs, x ≤ h)
    (hs : oldSum + xs.sum ≥ minSum)
    (hq : oldSq + (xs.map (· ^ 2)).sum ≥ minSq) :
    minSum ≤ oldSum + topSum xs.length h ∧ minSq ≤ oldSq + topSquare xs.length h := by
  obtain ⟨s, q⟩ := descending_weights_bounds xs h d b
  exact ⟨hs.trans (Nat.add_le_add_left s _), hq.trans (Nat.add_le_add_left q _)⟩

#print axioms descending_weights_bounds
#print axioms capacity_cut_sound

end NineSeparatedSubsetSums
