import FourColourCNF
import AllPublishedEdges

namespace CertifiedG449

def publishedPairs : List (Nat × Nat) :=
  G449OrbitArithmetic.allPublishedEdges.map fun e => (e.a,e.b)

def formula : List (List Int) := baseCNF 449 publishedPairs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in
theorem formula_count : formula.length = 9241 := by decide +kernel

theorem g449_no_proper_four_of_unsat (h : ∀ a, ¬ sat a formula) :
    ¬∃ c, proper c publishedPairs :=
  no_proper_four_of_base_unsat 449 publishedPairs h

def dimacs : String :=
  "p cnf 1796 " ++ toString formula.length ++ "\n" ++
    String.join (formula.map fun cl => String.intercalate " " (cl.map toString) ++ " 0\n")

#print axioms formula_count
#print axioms g449_no_proper_four_of_unsat
end CertifiedG449

