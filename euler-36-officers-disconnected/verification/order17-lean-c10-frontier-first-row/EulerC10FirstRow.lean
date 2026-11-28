import EulerRupFrontier

namespace Euler.RupFrontier.C10

def cl (s : List Int) : Sat.Clause := s.map Sat.Literal.ofInt

def c12732 : Sat.Clause := cl [1]
def c50 : Sat.Clause := cl [-1,1297]
def c12733 : Sat.Clause := cl [-1297,1298,1299,1300,1301,1302,-9721]
def c15051 : Sat.Clause := cl [1298,1299,1300,1301,1302,-9721]

/-- The first positive RUP row after the opening C10 deletion row.
The implication is independent of clause IDs and of the original CNF.
Its exact inputs become hypotheses, then the two nested implications
perform the two unit propagations before the conflict clause. -/
theorem firstRow_implies (v : Sat.Valuation)
    (one : v.satisfies c12732) (next : v.satisfies c50) (last : v.satisfies c12733) :
    v.satisfies c15051 := by
  change (¬ v 0) → False at one
  change v 0 → (¬ v 1296) → False at next
  change v 1296 → (¬ v 1297) → (¬ v 1298) → (¬ v 1299) →
    (¬ v 1300) → (¬ v 1301) → v 9720 → False at last
  change (¬ v 1297) → (¬ v 1298) → (¬ v 1299) →
    (¬ v 1300) → (¬ v 1301) → v 9720 → False
  intro h1298 h1299 h1300 h1301 h1302 h9721
  exact one (fun h1 => next h1 (fun h1297 =>
    last h1297 h1298 h1299 h1300 h1301 h1302 h9721))

def firstInputs : Frontier := [(12732,c12732),(50,c50),(12733,c12733)]
def firstOutputs : Frontier := [(15051,c15051)]

theorem firstSlice : Transformer firstInputs firstOutputs := by
  intro row hrow
  simp only [firstOutputs,List.mem_singleton] at hrow
  subst row
  intro v h
  apply firstRow_implies v
  · exact h.1 c12732 (by simp [frontierFormula,firstInputs])
  · exact h.1 c50 (by simp [frontierFormula,firstInputs])
  · exact h.1 c12733 (by simp [frontierFormula,firstInputs])

/-- With exact proofs of the three named clauses from a common base
context, the derived row can be handed to the following slice. -/
theorem firstRow_from_base (base : Sat.Fmla)
    (h : Derived base firstInputs) : base.proof c15051 :=
  apply_transformer firstSlice h (15051,c15051) (by simp [firstOutputs])

#print axioms firstRow_implies
#print axioms firstSlice
#print axioms firstRow_from_base
end Euler.RupFrontier.C10
