import EulerBatch.ContainmentDriver
import EulerBatch.C08CoreSorted
namespace Euler.Batch.C08
prove_numbered_containment branchFullFormula branchContainsCore branchFullUnsat coreUnsat
  10646 60567 5788 (include_str "cases/08/original.cnf") (include_str "../alternatives/08/1.cnf")

theorem branchNoAssignment :
    ¬ ∃ v : Sat.Valuation, v.satisfies_fmla branchFullFormula := by
  rintro ⟨v,hv⟩
  exact branchFullUnsat v hv
#print axioms branchNoAssignment
#print axioms branchContainsCore
#print axioms branchFullUnsat
end Euler.Batch.C08
