import LatinGap
import Mathlib.Data.Fintype.Pi

/-!
# Euler's 36 officers

A maximal partial arrangement can have 18 officers. The construction uses
two disjoint order-three orthogonal pairs.
-/

open Finset
open LatinGap

namespace EulerOfficers

/-- Give the two blocks disjoint, consecutive ranges of three labels. -/
private def label (b : Fin 2) (a : Fin 3) : Fin 6 :=
  ⟨3*b.val+a.val, by have := b.isLt; have := a.isLt; omega⟩

/-- In block (b), the four coordinates are (x,y,x+y,x+2y) modulo three. -/
private def officer (p : Fin 2 × Fin 3 × Fin 3) : Word 6 :=
  fun i => label p.1 (if i = 0 then p.2.1 else if i = 1 then p.2.2 else
    if i = 2 then p.2.1 + p.2.2 else p.2.1 + 2*p.2.2)

/-- The union of the two explicit order-three designs. -/
def arrangement : Design 6 := univ.image officer

/-- The construction contains all 18 officers specified by the formula. -/
theorem arrangement_card : arrangement.card = 18 := by decide

/-- Each of the twelve ordered pair projections has 18 distinct values. -/
private theorem projection_card (i j : Coord) (hij : i ≠ j) :
    (arrangement.image fun w => (w i, w j)).card = 18 := by
  fin_cases i <;> fin_cases j <;> first | contradiction | decide

/-- Each pair of coordinates determines the officer uniquely. -/
theorem arrangement_linear : Linear arrangement := by
  intro u hu v hv i j hij hi hj
  exact (injOn_of_card_image_eq ((projection_card i j hij).trans arrangement_card.symm))
    hu hv (Prod.ext hi hj)

/-- Every pair of values in the same block is used across distinct coordinates. -/
private theorem same_block_pair :
    ∀ (i j : Coord) (a b : Fin 6), i ≠ j → a.val / 3 = b.val / 3 →
      Used arrangement (i, a) (j, b) := by
  change ∀ (i j : Coord) (a b : Fin 6), i ≠ j → a.val / 3 = b.val / 3 →
    i ≠ j ∧ ∃ w ∈ arrangement, w i = a ∧ w j = b
  decide

/-- Four labels drawn from two blocks always repeat a block in two coordinates. -/
theorem arrangement_saturated : Saturated arrangement := by
  intro w
  let b (i : Coord) : Fin 2 := ⟨(w i).val / 3, by have := (w i).isLt; omega⟩
  obtain ⟨i, j, hij, hb⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt b (by decide)
  exact ⟨i, j, same_block_pair i j (w i) (w j) hij (congrArg Fin.val hb)⟩

/-- The upper endpoint of the current bounds follows from a Lean-checked witness. -/
theorem exists_maximal_eighteen :
    ∃ D : Design 6, Linear D ∧ Saturated D ∧ D.card = 18 :=
  ⟨arrangement, arrangement_linear, arrangement_saturated, arrangement_card⟩

end EulerOfficers

#print axioms EulerOfficers.exists_maximal_eighteen
