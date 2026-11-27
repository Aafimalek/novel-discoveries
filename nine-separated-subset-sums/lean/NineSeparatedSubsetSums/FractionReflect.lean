import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Basic.Real.Basic

namespace NineSeparatedSubsetSums

/-- Reflecting at an integer plus delta cannot hide a fractional part
larger than delta. -/
theorem fract_le_of_reflected_fract_le (K : ℤ) (δ x : ℝ)
    (hδ : 0 ≤ δ)
    (hother : Int.fract ((K : ℝ) + δ - x) ≤ δ) :
    Int.fract x ≤ δ := by
  by_contra! h
  have hlt := Int.fract_lt_one x
  let j : ℤ := K - Int.floor x - 1
  have hj : Int.floor ((K : ℝ) + δ - x) = j := by
    apply Int.floor_eq_iff.mpr
    dsimp [j]
    push_cast
    unfold Int.fract at h hlt
    constructor <;> linarith
  unfold Int.fract at hother hlt
  rw [hj] at hother
  dsimp [j] at hother
  push_cast at hother
  linarith

#print axioms fract_le_of_reflected_fract_le

end NineSeparatedSubsetSums

