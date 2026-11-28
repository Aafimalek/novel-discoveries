/- Static forward bridge. No compiler has run on this source. -/
import ES33.EndpointExclusionGeometry
import RealChainValuation
import ActualRealConnector

namespace ES33.EndpointConcrete

open ES33.Numbering
open VerificationGoals

/-- Exact residual avoidance excludes all three forbidden endpoint
families using the same chain-existence valuation that satisfies P. -/
theorem chainVal_excludes32 {χ : Endpoint.Signs 32} (h : Residual32 χ) :
    EndpointGuard.PrunedExclusions 7 7 6 (Mapped (chainVal χ)) := by
  obtain ⟨hχ,havoid,hpos⟩ := h
  have heven := (Anchor.avoidanceClauses_iff χ).mp havoid
  refine ⟨?_,?_,?_⟩
  · intro a c fits bad
    have cap := (chainVal_cap_pair χ 7 a c).mp bad
    have cup := (Endpoint.ends_two_iff χ true a c).mpr fits.1
    exact heven (Endpoint.even_set_of_endpoint_pair hχ
      (by decide) (by decide) (by decide) cap cup)
  · intro a c _ bad
    exact hpos (Endpoint.positive_set_of_cup hχ (by decide)
      ((chainVal_cup_pair χ 6 a c).mp bad))
  · rintro s t a c hs ht _ _ hk ⟨cap,cup⟩
    exact heven (Endpoint.even_set_of_endpoint_pair hχ hs.2.1 ht.2.1 hk
      ((chainVal_cap_pair χ s a c).mp cap) ((chainVal_cup_pair χ t a c).mp cup))

/-- No auxiliary assumptions: any actual real residual witness satisfies
the internal typed compiler's exact numbered target. -/
theorem real_residual_satisfies_target32 (p : Fin 32 ↪ Plane)
    (h : GeometricReflection.RealWitness p) :
    ∃ a, NumberedSatisfies a
      (compile (dictionary 32 7 6) (typedRows 32 7 7 6) target32_covered) :=
  target32_numbered_of_real_residual p h (chainVal (orientations p))
    (chainVal_signs _) (real_chainVal_propagates p h.2.2.1) (chainVal_excludes32 h.2.2)

/-- Conditional ES33 result for the precise internal compiled object.
No external DIMACS equality, certificate, or UNSAT claim is asserted. -/
theorem es33_of_internal_target32_unsat
    (unsat : ¬ ∃ a, NumberedSatisfies a
      (compile (dictionary 32 7 6) (typedRows 32 7 7 6) target32_covered))
    (p : Fin 33 ↪ Plane) (gp : GeneralPositionAll p) :
    ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s := by
  by_contra bad
  obtain ⟨r,hr⟩ := GeometricReflection.es33_counterexample_gives_real_witness p gp bad
  exact unsat (real_residual_satisfies_target32 r hr)

#print axioms chainVal_excludes32
#print axioms real_residual_satisfies_target32
#print axioms es33_of_internal_target32_unsat

end ES33.EndpointConcrete
