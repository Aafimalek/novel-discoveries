/- Static draft: preserves all missing hypotheses explicitly. -/
import LiteralFamilies
import RealResidualExtraction

namespace ES33.EndpointConcrete

open ES33.Numbering ES33.EndpointGuard
open VerificationGoals

/-- If the chosen valuation is the real residual's orientation bits and
its auxiliary bits meet the guarded families, every compiled clause is
satisfied. The mechanical generator and semantic-auxiliary proof are
distinct prerequisites; neither is asserted here. -/
theorem numbered_of_real_residual (p : Fin 32 ↪ Plane)
    (h : GeometricReflection.RealWitness p) (v : Key 32 → Bool)
    (onSigns : signVal v = orientations p)
    (P : PrunedPropagation (signVal v) 7 6 (Mapped v))
    (X : PrunedExclusions 7 7 6 (Mapped v))
    (cover : covered 32 7 7 6) (good : GoodRows 32 7 7 6) :
    ∃ a, NumberedSatisfies a
      (compile (dictionary 32 7 6) (typedRows 32 7 7 6) cover) := by
  apply numbered_of_guarded cover good ?_ P X
  rw [onSigns]
  exact h.2.2.1

#print axioms numbered_of_real_residual

end ES33.EndpointConcrete
