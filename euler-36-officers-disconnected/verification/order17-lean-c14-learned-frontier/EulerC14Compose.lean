import EulerC14Producer
import EulerC14Consumer

namespace Euler.RupFrontier.C14

/-- Exact learned clauses proved in one independently compiled slice
provide the entire typed input of the next. -/
theorem composed : Transformer inputs output :=
  transformer_comp Producer.step Consumer.step

theorem fromCommonBase (f : Sat.Fmla) (ready : Derived f inputs) :
    Derived f output :=
  apply_transformer composed ready

#print axioms composed
#print axioms fromCommonBase
end Euler.RupFrontier.C14
