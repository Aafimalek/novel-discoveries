import NineSeparatedSubsetSums.CubeFinsetEncoding
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Basic

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- Relabeling coordinates preserves the separation hypothesis on all
ordinary finite subset sums. -/
theorem subset_separation_reindex {α : Type*} [DecidableEq α]
    (p : Equiv.Perm α) (w : α → ℝ)
    (sep : ∀ A B : Finset α, A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∀ A B : Finset α, A ≠ B →
      1 ≤ |(∑ i ∈ A, w (p i)) - (∑ i ∈ B, w (p i))| := by
  intro A B h
  have hm : A.map p.toEmbedding ≠ B.map p.toEmbedding :=
    fun h' => h (Finset.map_injective p.toEmbedding h')
  simpa only [Finset.sum_map, Equiv.toEmbedding_apply] using
    sep (A.map p.toEmbedding) (B.map p.toEmbedding) hm

/-- By swapping a maximal coordinate with the last coordinate, one can
take the final coordinate to be largest without losing separation. -/
theorem reindex_max_last {n : ℕ} (w : Fin (n+1) → ℝ)
    (sep : ∀ A B : Finset (Fin (n+1)), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ p : Equiv.Perm (Fin (n+1)),
      (∀ i, w (p i) ≤ w (p (Fin.last n))) ∧
      (∀ A B : Finset (Fin (n+1)), A ≠ B →
        1 ≤ |(∑ i ∈ A, w (p i)) - (∑ i ∈ B, w (p i))|) := by
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (n+1))) w ⟨Fin.last n, Finset.mem_univ _⟩
  let p := Equiv.swap (Fin.last n) m
  refine ⟨p, ?_, subset_separation_reindex p w sep⟩
  intro i
  exact (hm (p i) (Finset.mem_univ _)).trans_eq
    (congrArg w (Equiv.swap_apply_left (Fin.last n) m)).symm

/-- If the last coordinate is largest, every earlier coordinate is at
least a unit below it by applying separation to the two singleton sums. -/
theorem earlier_le_last_sub_one {n : ℕ} (w : Fin (n+1) → ℝ)
    (largest : ∀ i, w i ≤ w (Fin.last n))
    (sep : ∀ A B : Finset (Fin (n+1)), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|)
    (i : Fin n) : w i.castSucc ≤ w (Fin.last n) - 1 := by
  have he : i.castSucc ≠ Fin.last n := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = n at hv
    omega
  have hes : ({i.castSucc} : Finset (Fin (n+1))) ≠ {Fin.last n} :=
    fun h => he (Finset.singleton_injective h)
  have hs := sep {i.castSucc} {Fin.last n} hes
  simp only [Finset.sum_singleton, abs_of_nonpos (sub_nonpos.mpr (largest i.castSucc)), neg_sub] at hs
  linarith

#print axioms subset_separation_reindex
#print axioms reindex_max_last
#print axioms earlier_le_last_sub_one

end NineSeparatedSubsetSums
