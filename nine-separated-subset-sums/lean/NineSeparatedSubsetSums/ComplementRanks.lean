import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

namespace NineSeparatedSubsetSums

/-- Complementation turns the first critical rank interval into the second.
The intervals overlap, so the offset holds everywhere in their union.
Ranks are zero-based. -/
theorem complement_ranks_extend_offset (a : ℕ → ℤ) (T K : ℤ)
    (hcomp : ∀ i : ℕ, i ≤ 511 → a (511 - i) = T - a i)
    (hfirst : ∀ i : ℕ, 157 ≤ i → i ≤ 305 → (i : ℤ) - a i = K) :
    (∀ i : ℕ, 157 ≤ i → i ≤ 354 → (i : ℤ) - a i = K) ∧
    2 * a 157 = T - 197 ∧ 2 * a 354 = T + 197 := by
  have reflect (i : ℕ) (hi : 206 ≤ i) (hi' : i ≤ 354) :
      (i : ℤ) - a i = 511 - T - K := by
    have e := hcomp (511 - i) (by omega)
    have he : 511 - (511 - i) = i := by omega
    rw [he] at e
    have hc := hfirst (511 - i) (by omega) (by omega)
    omega
  have heq : 511 - T - K = K := by
    have h1 := reflect 206 (by omega) (by omega)
    have h2 := hfirst 206 (by omega) (by omega)
    omega
  have extn (i : ℕ) (hi : 157 ≤ i) (hi' : i ≤ 354) : (i : ℤ) - a i = K := by
    by_cases h : i ≤ 305
    · exact hfirst i hi h
    · rw [reflect i (by omega) hi', heq]
  refine ⟨extn, ?_, ?_⟩
  · have h1 := extn 157 (by omega) (by omega)
    omega
  · have h1 := extn 354 (by omega) (by omega)
    omega

#print axioms complement_ranks_extend_offset

end NineSeparatedSubsetSums
