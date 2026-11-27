import TwoByThreeReplay
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace TwoByThreeReplay

abbrev Profiles := Fin 10 → Fin 7 → ℕ

def toCutoffWeights (q : Profiles) : Profiles := fun p k =>
  (![q p 0 - q p 1, q p 1 - q p 2, q p 2 - q p 3,
    q p 3 - q p 4, q p 4 - q p 5, q p 5 - q p 6, q p 6] : Fin 7 → ℕ) k

private theorem sumFinSeven {M : Type*} [AddCommMonoid M] (f : Fin 7 → M) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp [Fin.sum_univ_succ, add_assoc]

theorem eq_sum_toCutoffWeights (q : Profiles) (hq : ∀ p, Antitone (q p)) (p : Fin 10) (j : Fin 7) :
    ∑ k : Fin 7, (if j ≤ k then toCutoffWeights q p k else 0) = q p j := by
  have h01 := hq p (show (0 : Fin 7) ≤ 1 by decide)
  have h12 := hq p (show (1 : Fin 7) ≤ 2 by decide)
  have h23 := hq p (show (2 : Fin 7) ≤ 3 by decide)
  have h34 := hq p (show (3 : Fin 7) ≤ 4 by decide)
  have h45 := hq p (show (4 : Fin 7) ≤ 5 by decide)
  have h56 := hq p (show (5 : Fin 7) ≤ 6 by decide)
  rw [sumFinSeven]
  fin_cases j <;>
    simp only [toCutoffWeights] <;>
    simp (config := {decide := true}) <;> omega

private theorem left_cut_sum :
    ∀ (k r : Fin 7), min (k.val+1) (r.val+1) =
      ∑ j : Fin 7, if j ≤ k ∧ j.val ≤ r.val then 1 else 0 := by decide

private theorem right_cut_sum :
    ∀ (k r : Fin 7), k.val+1 - min (k.val+1) (r.val+1) =
      ∑ j : Fin 7, if j ≤ k ∧ r.val < j.val then 1 else 0 := by decide

private theorem branchRank_bound : ∀ p : Fin 10, ∀ u : Fin 7,
    u ≠ 6 → branchRank p u < 7 := by decide

private theorem cut_before_branch (p : Fin 10) (j u : Fin 7) (hu : u ≠ 6) :
    rank p j 6 < rank p j u ↔ j.val ≤ branchRank p u := by
  simp only [rank, ite_true, ite_eq_right hu]
  split <;> omega

private theorem branch_before_cut (p : Fin 10) (j u : Fin 7) (hu : u ≠ 6) :
    rank p j u < rank p j 6 ↔ branchRank p u < j.val := by
  simp only [rank, ite_true, ite_eq_right hu]
  by_cases h : j.val ≤ branchRank p u <;> simp only [h, ite_true, ite_false] <;> omega

private theorem branch_before_branch (p : Fin 10) (j u v : Fin 7)
    (hu : u ≠ 6) (hv : v ≠ 6) :
    rank p j u < rank p j v ↔ branchRank p u < branchRank p v := by
  simp only [rank, ite_eq_right hu, ite_eq_right hv]
  split <;> split <;> omega

private theorem size_as_sum : ∀ k : Fin 7, k.val+1 = ∑ j : Fin 7, if j ≤ k then 1 else 0 := by
  decide

theorem component_as_sum (p : Fin 10) (k u v : Fin 7) :
    component p k u v =
      ∑ j : Fin 7, if j ≤ k ∧ rank p j u < rank p j v then 1 else 0 := by
  by_cases hu : u = 6
  · subst u
    by_cases hv : v = 6
    · subst v; simp [component]
    · simp only [component, ite_true, ite_eq_right hv, cut_before_branch p _ v hv]
      let r : Fin 7 := ⟨branchRank p v, branchRank_bound p v hv⟩
      exact left_cut_sum k r
  · by_cases hv : v = 6
    · subst v
      simp only [component, ite_eq_right hu, ite_true, branch_before_cut p _ u hu]
      let r : Fin 7 := ⟨branchRank p u, branchRank_bound p u hu⟩
      exact right_cut_sum k r
    · simp only [component, ite_eq_right hu, ite_eq_right hv, branch_before_branch p _ u v hu hv]
      by_cases h : branchRank p u < branchRank p v
      · simpa [h] using size_as_sum k
      · simp [h]

def binMass (q : Profiles) : ℕ := ∑ p : Fin 10, ∑ j : Fin 7, q p j
def binCount (q : Profiles) (u v : Fin 7) : ℕ :=
  ∑ p : Fin 10, ∑ j : Fin 7, if rank p j u < rank p j v then q p j else 0

def modelMass (w : Profiles) : ℕ := ∑ p : Fin 10, ∑ k : Fin 7, (k.val+1) * w p k
def modelCount (w : Profiles) (u v : Fin 7) : ℕ :=
  ∑ p : Fin 10, ∑ k : Fin 7, component p k u v * w p k

theorem weightedMass_eq (q : Profiles) (hq : ∀ p, Antitone (q p)) :
    modelMass (toCutoffWeights q) = binMass q := by
  unfold modelMass binMass
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [size_as_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← eq_sum_toCutoffWeights q hq p j]
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp_all

theorem weightedCount_eq (q : Profiles) (hq : ∀ p, Antitone (q p)) (u v : Fin 7) :
    modelCount (toCutoffWeights q) u v = binCount q u v := by
  unfold modelCount binCount
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [component_as_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← eq_sum_toCutoffWeights q hq p j]
  split
  · rename_i h
    apply Finset.sum_congr rfl
    intro k _
    simp [h]
  · rename_i h
    simp [h]

/-- An antitone profile with zero mass on a forbidden order yields cutoff
weights with zero mass on that order. -/
theorem toCutoffWeights_zero (q : Profiles) (p : Fin 10)
    (h : ∀ j, q p j = 0) (k : Fin 7) : toCutoffWeights q p k = 0 := by
  fin_cases k <;> simp [toCutoffWeights, h]

#print axioms weightedMass_eq
#print axioms weightedCount_eq
#print axioms toCutoffWeights_zero
end TwoByThreeReplay
