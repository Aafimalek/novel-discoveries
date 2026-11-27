import EulerBatch.ContainmentDriver
import EulerBatch.C13CoreSorted
namespace Euler.Batch.C13
prove_numbered_containment branchFullFormula branchContainsCore branchFullUnsat coreUnsat
  10646 60248 6937 (include_str "cases/13/original.cnf") (include_str "../alternatives/13/1.cnf")

theorem branchNoAssignment :
    ¬ ∃ v : Sat.Valuation, v.satisfies_fmla branchFullFormula := by
  rintro ⟨v,hv⟩
  exact branchFullUnsat v hv
#print axioms branchNoAssignment
#print axioms branchContainsCore
#print axioms branchFullUnsat
end Euler.Batch.C13
