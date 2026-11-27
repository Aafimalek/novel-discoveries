import TwoArmsMix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace TwoArmsMix

def toWeights (q : Weights) : Weights := fun p k =>
  (![q p 0 - q p 1, q p 1 - q p 2, q p 2 - q p 3,
    q p 3 - q p 4, q p 4 - q p 5, q p 5] : Fin 6 → ℕ) k

private theorem sumFinSix {M : Type*} [AddCommMonoid M] (f : Fin 6 → M) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ, add_assoc]

theorem eq_sum_toWeights (q : Weights) (hq : ∀ p, Antitone (q p)) (p j : Fin 6) :
    ∑ k : Fin 6, (if j ≤ k then toWeights q p k else 0) = q p j := by
  have h01 := hq p (show (0 : Fin 6) ≤ 1 by decide)
  have h12 := hq p (show (1 : Fin 6) ≤ 2 by decide)
  have h23 := hq p (show (2 : Fin 6) ≤ 3 by decide)
  have h34 := hq p (show (3 : Fin 6) ≤ 4 by decide)
  have h45 := hq p (show (4 : Fin 6) ≤ 5 by decide)
  rw [sumFinSix]
  fin_cases j <;>
    simp only [toWeights] <;>
    simp (config := {decide := true}) <;> omega

private theorem component_as_sum :
    ∀ p k u v : Fin 6, component p k u v =
      ∑ j : Fin 6, if j ≤ k ∧ rank p j u < rank p j v then 1 else 0 := by
  decide

private theorem size_as_sum : ∀ k : Fin 6, k.val+1 = ∑ j : Fin 6, if j ≤ k then 1 else 0 := by
  decide

def binMass (q : Weights) : ℕ := ∑ p : Fin 6, ∑ j : Fin 6, q p j
def binCount (q : Weights) (u v : Fin 6) : ℕ :=
  ∑ p : Fin 6, ∑ j : Fin 6, if rank p j u < rank p j v then q p j else 0

theorem weightedMass_eq (q : Weights) (hq : ∀ p, Antitone (q p)) :
    mass (toWeights q) = binMass q := by
  unfold mass binMass
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [size_as_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← eq_sum_toWeights q hq p j]
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp_all

theorem weightedCount_eq (q : Weights) (hq : ∀ p, Antitone (q p)) (u v : Fin 6) :
    count (toWeights q) u v = binCount q u v := by
  unfold count binCount
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [component_as_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← eq_sum_toWeights q hq p j]
  split
  · rename_i h
    apply Finset.sum_congr rfl
    intro k _
    simp [h]
  · rename_i h
    simp [h]

/-- The bin formulation uses only six componentwise-antitone profiles. -/
theorem balanced_quarter_bins (q : Weights) (hq : ∀ p, Antitone (q p))
    (hcap : 4 * binCount q 5 0 ≤ binMass q) :
    ∃ u v, u ≠ v ∧ binMass q ≤ 3 * binCount q u v ∧
      3 * binCount q u v ≤ 2 * binMass q := by
  have hc : 4 * count (toWeights q) 5 0 ≤ mass (toWeights q) := by
    simpa only [weightedCount_eq q hq, weightedMass_eq q hq] using hcap
  obtain ⟨u, v, huv⟩ := balanced_quarter (toWeights q) hc
  exact ⟨u, v, by simpa [Balanced, weightedCount_eq q hq, weightedMass_eq q hq] using huv⟩

#print axioms balanced_quarter_bins
end TwoArmsMix
