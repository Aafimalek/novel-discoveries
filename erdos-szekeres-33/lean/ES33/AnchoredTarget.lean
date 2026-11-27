import ES33.ProjectiveAnchor
import ES33.AnchorReduction

namespace ES33

/-- Exact abstract assumptions on the reduced 32-point assignment. -/
def Residual32 (r : Anchor.Signs 32) : Prop :=
  SignotopeConstraints 32 r ∧ AvoidanceClauses 32 r ∧ ¬ Anchor.HasPositiveSet r 6

/-- A real 33-point counterexample induces a 32-label signotope with
neither an even-parity seven-set nor a positive six-set. -/
theorem es33_counterexample_gives_residual (p : Fin 33 ↪ Plane) (gp : GeneralPositionAll p)
    (h : ¬ ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s) :
    ∃ r : Anchor.Signs 32, Residual32 r := by
  obtain ⟨χ,hχ,ha,h0⟩ :=
    geometric_counterexample_gives_positive_anchor (n := 32) p gp h
  exact Anchor.anchored_ES33_iff_residual.mp ⟨χ,h0,hχ,ha⟩

/-- This theorem is conditional on excluding every residual signotope.
No satisfiability or realizability converse is asserted for real data. -/
theorem es33_of_residual_unsat (unsat : ¬ ∃ r : Anchor.Signs 32, Residual32 r)
    (p : Fin 33 ↪ Plane) (gp : GeneralPositionAll p) :
    ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s := by
  by_contra h
  exact unsat (es33_counterexample_gives_residual p gp h)

#print axioms es33_counterexample_gives_residual
#print axioms es33_of_residual_unsat

end ES33
