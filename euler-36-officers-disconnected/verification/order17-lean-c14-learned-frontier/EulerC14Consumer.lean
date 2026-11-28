import EulerRupSliceDriver
import EulerC14FrontierData
namespace Euler.RupFrontier.C14.Consumer

frontier_rup checked 1 rawBoundary (include_str "consumer.lrat")

theorem exact_input_formula : checked.cnf = frontierFormula boundary := by rfl

theorem step : Transformer boundary output := by
  intro row hm
  simp only [output,rawOutput,signedRows,List.map_cons,List.map_nil,
    List.mem_cons,List.mem_nil_iff,or_false] at hm
  subst row
  rw [← exact_input_formula]
  exact checked.row_11163

#print axioms exact_input_formula
#print axioms step
end Euler.RupFrontier.C14.Consumer
