import NineSeparatedSubsetSums.Weighted
import Mathlib.Algebra.Order.Floor.Ring

namespace NineSeparatedSubsetSums

theorem subinterval_rank_bounds (v : ℕ → ℝ) (bound L R i j : ℕ)
    (hgap : ∀ k : ℕ, k + 1 < bound → 1 ≤ v (k + 1) - v k)
    (hL : L ≤ i) (hij : i ≤ j) (hR : j ≤ R) (hb : R < bound) :
    ((j - i : ℕ) : ℝ) ≤ v j - v i ∧
      v j - v i ≤ ((j - i : ℕ) : ℝ) + (v R - v L - ((R - L : ℕ) : ℝ)) := by
  have a := accumulate_gaps v bound hgap L (i - L) (by omega)
  have b := accumulate_gaps v bound hgap i (j - i) (by omega)
  have c := accumulate_gaps v bound hgap j (R - j) (by omega)
  have ai : L + (i - L) = i := by omega
  have bj : i + (j - i) = j := by omega
  have cr : j + (R - j) = R := by omega
  rw [ai] at a
  rw [bj] at b
  rw [cr] at c
  refine ⟨b, ?_⟩
  have hlen : (R - L : ℕ) = (i - L) + (j - i) + (R - j) := by omega
  have hcast : ((R - L : ℕ) : ℝ) =
      ((i - L : ℕ) : ℝ) + ((j - i : ℕ) : ℝ) + ((R - j : ℕ) : ℝ) := by
    exact_mod_cast hlen
  linarith

/-- If a block has less than one extra unit of spacing, flooring any
forward difference in it returns the rank difference. -/
theorem rank_difference_is_floor (v : ℕ → ℝ) (bound L R i j : ℕ)
    (hgap : ∀ k : ℕ, k + 1 < bound → 1 ≤ v (k + 1) - v k)
    (hL : L ≤ i) (hij : i ≤ j) (hR : j ≤ R) (hb : R < bound)
    (hexcess : v R - v L - ((R - L : ℕ) : ℝ) < 1) :
    Int.floor (v j - v i) = ((j - i : ℕ) : ℤ) := by
  obtain ⟨ha, hu⟩ := subinterval_rank_bounds v bound L R i j hgap hL hij hR hb
  apply Int.floor_eq_iff.mpr
  constructor
  · exact_mod_cast ha
  · norm_num
    linarith

#print axioms rank_difference_is_floor

end NineSeparatedSubsetSums

