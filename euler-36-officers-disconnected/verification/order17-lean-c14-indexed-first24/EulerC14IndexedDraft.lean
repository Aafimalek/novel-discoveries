import Mathlib.Tactic.Sat.FromLRAT
/-!
Static design only: intentionally NOT compiled or represented as checked.
Dense original positions are DIMACS id - 1; learned positions are
core length + the zero-based addition ordinal. IDs are audit metadata;
the kernel-visible contract is always an exact clause at an exact slot.
-/

namespace Euler.C14.IndexedDraft

/-- Not an association list: the intended implementation is a transparent
    fixed-size block directory with static leaves for the exact clauses.
    The source array is separately related to the original parsed CNF. -/
abbrev ClauseAt := Nat → Sat.Clause

/-- Monotone semantic knowledge, not an asserted archive correctness.
    Keeping logically derived clauses after LRAT deletion is sound for
    pure positive-hint RUP; the raw liveness audit remains separate. -/
def GoodBelow (base : Sat.Fmla) (atSlot : ClauseAt) (bound : Nat) : Prop :=
  ∀ j : Nat, j < bound → base.proof (atSlot j)

/-- Contract for each separately compiled artifact. A theorem type is small
    irrespective of the number of original or carried clauses. -/
def Slice (base : Sat.Fmla) (atSlot : ClauseAt) (lo hi : Nat) : Prop :=
  GoodBelow base atSlot lo → GoodBelow base atSlot hi

theorem extend {base : Sat.Fmla} {atSlot : ClauseAt} {j : Nat}
    (step : GoodBelow base atSlot j → base.proof (atSlot j)) :
    Slice base atSlot j (j + 1) := by
  intro h i hi
  by_cases hlt : i < j
  · exact h i hlt
  · have hj : i = j := Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.le_of_not_gt hlt)
    subst i
    exact step h

theorem compose {base : Sat.Fmla} {atSlot : ClauseAt} {i j k : Nat}
    (ab : Slice base atSlot i j) (bc : Slice base atSlot j k) :
    Slice base atSlot i k :=
  fun h => bc (ab h)

/-- The one original-context bridge. In production this can be proved from
    a single aligned vector or balanced tree, not a separate linear
    List.mem search for each lookup. This draft intentionally provides
    no premise-free certifier of archived row contents. -/
theorem init {base : Sat.Fmla} {atSlot : ClauseAt}
    (aligned : ∀ j, j < base.length → base[j]? = some (atSlot j)) :
    GoodBelow base atSlot base.length := by
  intro j hj v hv
  exact hv.1 _ (List.mem_of_getElem? (aligned j hj))

theorem finish {base : Sat.Fmla} {atSlot : ClauseAt} {bound slot : Nat}
    (ready : GoodBelow base atSlot bound) (inside : slot < bound)
    (empty : atSlot slot = Sat.Clause.nil) :
    base.proof Sat.Clause.nil := by
  rw [← empty]
  exact ready slot inside

end Euler.C14.IndexedDraft
