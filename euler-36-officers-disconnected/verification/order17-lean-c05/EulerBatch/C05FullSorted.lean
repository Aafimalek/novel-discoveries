import EulerBatch.ContainmentDriver
import EulerBatch.C05CoreSorted
namespace Euler.Batch.C05
prove_numbered_containment branchFullFormula branchContainsCore branchFullUnsat coreUnsat
  10646 60567 5036 (include_str "cases/05/original.cnf") (include_str "../alternatives/05/1.cnf")

theorem branchNoAssignment :
    ¬ ∃ v : Sat.Valuation, v.satisfies_fmla branchFullFormula := by
  rintro ⟨v,hv⟩
  exact branchFullUnsat v hv
#print axioms branchNoAssignment
#print axioms branchContainsCore
#print axioms branchFullUnsat
end Euler.Batch.C05
