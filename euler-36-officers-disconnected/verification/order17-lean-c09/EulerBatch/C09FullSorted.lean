import EulerBatch.ContainmentDriver
import EulerBatch.C09CoreSorted
namespace Euler.Batch.C09
prove_numbered_containment branchFullFormula branchContainsCore branchFullUnsat coreUnsat
  10646 60567 5649 (include_str "cases/09/original.cnf") (include_str "../alternatives/09/1.cnf")

theorem branchNoAssignment :
    ¬ ∃ v : Sat.Valuation, v.satisfies_fmla branchFullFormula := by
  rintro ⟨v,hv⟩
  exact branchFullUnsat v hv
#print axioms branchNoAssignment
#print axioms branchContainsCore
#print axioms branchFullUnsat
end Euler.Batch.C09
