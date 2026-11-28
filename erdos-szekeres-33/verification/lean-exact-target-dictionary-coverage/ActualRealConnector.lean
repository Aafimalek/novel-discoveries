import ActualCoverage
import RealLiteralConnector

namespace ES33.EndpointConcrete

open ES33.Numbering ES33.EndpointGuard
open VerificationGoals

/-- If auxiliary bits satisfying the guarded endpoint propagation and
exclusions can be supplied for this real residual, it satisfies the exact
typed generator's compiled numbered formula. There is no hypothesis about
row exhaustiveness or dictionary coverage. External file identity is not
asserted here. -/
theorem target32_numbered_of_real_residual (p : Fin 32 ↪ Plane)
    (h : GeometricReflection.RealWitness p) (v : Key 32 → Bool)
    (onSigns : signVal v = orientations p)
    (P : PrunedPropagation (signVal v) 7 6 (Mapped v))
    (X : PrunedExclusions 7 7 6 (Mapped v)) :
    ∃ a, NumberedSatisfies a
      (compile (dictionary 32 7 6) (typedRows 32 7 7 6) target32_covered) :=
  numbered_of_real_residual p h v onSigns P X target32_covered target32_goodRows

#print axioms target32_numbered_of_real_residual

end ES33.EndpointConcrete
