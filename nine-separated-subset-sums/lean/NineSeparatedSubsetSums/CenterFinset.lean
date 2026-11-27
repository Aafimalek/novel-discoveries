import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- Approximate a target by a subset sum to within half a maximal step.
The target and the errors are doubled to avoid introducing fractions. -/
theorem exists_subset_near_double_sum {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (w : ι → ℤ) (M b : ℤ) (hM : 0 ≤ M)
    (hb : 0 ≤ b) (hb' : b ≤ 2 * ∑ x ∈ U, w x)
    (h : ∀ x ∈ U, 0 ≤ w x ∧ w x ≤ M) :
    ∃ V ⊆ U, -M ≤ 2 * (∑ x ∈ V, w x) - b ∧
      2 * (∑ x ∈ V, w x) - b ≤ M := by
  induction U using Finset.induction_on generalizing b with
  | empty =>
    simp only [Finset.sum_empty, mul_zero] at hb'
    exact ⟨∅, Finset.Subset.rfl, by simp; omega, by simp; omega⟩
  | @insert j U hj ih =>
    have hw := h j (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hj] at hb'
    by_cases hfirst : b ≤ 2 * w j
    · by_cases hsmall : b ≤ M
      · exact ⟨∅, Finset.empty_subset _, by simp; omega, by simp; omega⟩
      · exact ⟨{j}, Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _),
          by simpa only [Finset.sum_singleton] using (show -M ≤ 2 * w j - b by omega),
          by simpa only [Finset.sum_singleton] using (show 2 * w j - b ≤ M by omega)⟩
    · obtain ⟨V, hVU, hleft, hright⟩ :=
        ih (b - 2 * w j) (by omega) (by omega)
          (fun x hx => h x (Finset.mem_insert_of_mem hx))
      have hjV : j ∉ V := fun hm => hj (hVU hm)
      refine ⟨insert j V, Finset.insert_subset_insert j hVU, ?_, ?_⟩
      · rw [Finset.sum_insert hjV]; omega
      · rw [Finset.sum_insert hjV]; omega

#print axioms exists_subset_near_double_sum

end NineSeparatedSubsetSums
