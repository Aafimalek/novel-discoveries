import Mathlib.Tactic.Sat.FromLRAT

namespace Euler.RupFrontier

/-- An ID travels together with its concrete, ordered literal list. -/
abbrev Row := Nat × Sat.Clause
abbrev Frontier := List Row

def frontierFormula (frontier : Frontier) : Sat.Fmla :=
  frontier.map Prod.snd

/-- The original context proves this exact clause at each recorded ID. -/
def Derived (base : Sat.Fmla) (frontier : Frontier) : Prop :=
  ∀ r ∈ frontier, base.proof r.2

/-- A module representing a trace slice needs only its exact live-in
clause formula, not any earlier certificate module or the original CNF. -/
def Transformer (inputs outputs : Frontier) : Prop :=
  Derived (frontierFormula inputs) outputs

/-- Base-CNF positions must be checked when installing the initial
frontier; their integer IDs are not proofs of membership. -/
theorem derived_of_membership (base : Sat.Fmla) (frontier : Frontier)
    (h : ∀ r ∈ frontier, r.2 ∈ base) : Derived base frontier := by
  intro r hr v hv
  exact hv.1 _ (h r hr)

theorem frontier_self (frontier : Frontier) : Derived (frontierFormula frontier) frontier :=
  derived_of_membership _ _ (fun r hr => List.mem_map_of_mem hr)

theorem derived_of_append {base : Sat.Fmla} {left right : Frontier}
    (hl : Derived base left) (hr : Derived base right) :
    Derived base (left ++ right) := by
  intro row h
  exact (List.mem_append.mp h).elim (hl row) (hr row)

theorem derived_of_subset {base : Sat.Fmla} {old new : Frontier}
    (h : Derived base old) (small : ∀ r ∈ new, r ∈ old) : Derived base new :=
  fun r hr => h r (small r hr)

/-- Discharge the slice's live-in clauses from any common original
formula, using membership of the entire (ID, clause) pair. -/
theorem apply_transformer {base : Sat.Fmla} {inputs outputs : Frontier}
    (slice : Transformer inputs outputs) (ready : Derived base inputs) :
    Derived base outputs := by
  intro r hr v hv
  apply slice r hr v
  refine ⟨fun c hc => ?_⟩
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
  exact ready x hx v hv

theorem transformer_comp {a b c : Frontier}
    (ab : Transformer a b) (bc : Transformer b c) : Transformer a c :=
  apply_transformer bc ab

/-- An actual surviving empty clause finishes the original proof. -/
theorem original_refuted_of_empty {base : Sat.Fmla} {frontier : Frontier}
    (ready : Derived base frontier) (id : Nat) (hempty : (id,Sat.Clause.nil) ∈ frontier) :
    base.proof Sat.Clause.nil :=
  ready (id,Sat.Clause.nil) hempty

end Euler.RupFrontier
