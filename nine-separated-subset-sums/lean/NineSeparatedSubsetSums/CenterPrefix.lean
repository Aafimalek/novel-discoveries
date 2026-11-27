import Mathlib

namespace NineSeparatedSubsetSums

/-- An integer version of the prefix argument: find a prefix whose doubled
sum is within one step bound of any target in the doubled sum range. -/
theorem exists_prefix_near_double_sum
    (l : List ℤ) (M b : ℤ) (hM : 0 ≤ M)
    (hb₀ : 0 ≤ b) (hbMax : b ≤ 2 * l.sum)
    (hBound : ∀ x ∈ l, 0 ≤ x ∧ x ≤ M) :
    ∃ p q : List ℤ, l = p ++ q ∧
      -M ≤ 2 * p.sum - b ∧ 2 * p.sum - b ≤ M := by
  induction l generalizing b with
  | nil =>
      simp only [List.sum_nil, mul_zero] at hbMax
      refine ⟨[], [], rfl, ?_⟩
      simp only [List.sum_nil]
      omega
  | cons x xs ih =>
      have hx := hBound x (by simp)
      by_cases hfirst : b ≤ 2 * x
      · by_cases hsmall : b ≤ M
        · refine ⟨[], x :: xs, rfl, ?_⟩
          simp only [List.sum_nil]
          omega
        · refine ⟨[x], xs, rfl, ?_⟩
          simp only [List.sum_cons, List.sum_nil]
          omega
      · have hrest₀ : 0 ≤ b - 2 * x := by omega
        have hrestMax : b - 2 * x ≤ 2 * xs.sum := by
          simp only [List.sum_cons] at hbMax
          omega
        have hrestBound : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ M :=
          fun y hy => hBound y (by simp [hy])
        obtain ⟨p, q, hl, hlow, hhigh⟩ :=
          ih (b - 2 * x) hrest₀ hrestMax hrestBound
        refine ⟨x :: p, q, ?_, ?_⟩
        · simp only [List.cons_append, hl]
        · simp only [List.sum_cons]
          omega

#print axioms exists_prefix_near_double_sum
end NineSeparatedSubsetSums
