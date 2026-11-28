import EulerRupSliceDriver
import EulerC14FrontierData
namespace Euler.RupFrontier.C14.Producer

frontier_rup checked 2 rawInputs (include_str "producer.lrat")

theorem exact_input_formula : checked.cnf = frontierFormula inputs := by rfl

theorem step : Transformer inputs boundary := by
  intro row hm
  simp only [boundary,rawBoundary,signedRows,List.map_cons,List.map_nil,
    List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl | rfl
  · rw [← exact_input_formula]
    exact checked.row_10801
  · rw [← exact_input_formula]
    exact checked.row_10802

#print axioms exact_input_formula
#print axioms step
end Euler.RupFrontier.C14.Producer
