/- Static draft, awaiting strict replay. Exclusions are a separate geometric
step; this module gives the exact valuation and propagation only. -/
import LiteralFamilies
import ES33.EndpointModel

namespace ES33.EndpointConcrete

open VerificationGoals

/-- Exact sign-and-auxiliary valuation: the sign bits are the given
orientation map; all auxiliary bits are the truth of chain existence.
Classical decidability is for existence, not an unchecked computation. -/
noncomputable def chainVal {n : Nat} (χ : Endpoint.Signs n) : Key n → Bool := by
  classical
  exact fun
    | .sign a b c => χ a b c
    | .capLast d a b c => decide (Endpoint.EndState χ false d a b c)
    | .cupFirst d a b c => decide (Endpoint.StartState χ true d a b c)
    | .capPair d a c => decide (Endpoint.Ends χ false d a c)
    | .cupPair d a c => decide (Endpoint.Ends χ true d a c)

theorem chainVal_signs {n : Nat} (χ : Endpoint.Signs n) :
    signVal (chainVal χ) = χ := rfl

/-- The two developments use literally matching but independently
declared record types. This map simply copies the four predicate fields. -/
def guardStates {n : Nat} (M : Endpoint.States n) : EndpointGuard.States n :=
  ⟨M.capLast,M.cupFirst,M.capPair,M.cupPair⟩

/-- Lift all ten checked recurrence fields, without changing any range,
order, or color hypothesis. -/
theorem guard_propagation {n A B : Nat} {χ : Endpoint.Signs n}
    {M : Endpoint.States n} (P : Endpoint.Propagation χ A B M) :
    EndpointGuard.Propagation χ A B (guardStates M) :=
  ⟨P.capTwo,P.cupTwo,P.capThree,P.cupThree,P.capStep,P.cupStep,
    P.capProject,P.cupProject,P.capShorten,P.cupShorten⟩

/-- Before length-three aliasing, all four families agree on all indices
with the semantic chain predicates, including indices not emitted. -/
theorem chainVal_states {n : Nat} (χ : Endpoint.Signs n) :
    stateVal (chainVal χ) = guardStates (Endpoint.actual χ) := by
  simp only [stateVal,chainVal,guardStates,Endpoint.actual,decide_eq_true_eq]

/-- An emitted length-three cap literal agrees with the actual cap state
on an ordered triple. On unordered triples this need not be true. -/
theorem chainVal_cap_three {n : Nat} (χ : Endpoint.Signs n) {a b c : Fin n}
    (hab : a<b) (hbc : b<c) :
    (Mapped (chainVal χ)).capLast 3 a b c ↔ Endpoint.EndState χ false 3 a b c := by
  change χ a b c = false ↔ Endpoint.EndState χ false 3 a b c
  exact ⟨fun h => (Endpoint.end_base χ false a b c).mpr ⟨hab,hbc,h⟩,
    fun h => ((Endpoint.end_base χ false a b c).mp h).2.2⟩

/-- The matching length-three cup assertion uses a positive sign. -/
theorem chainVal_cup_three {n : Nat} (χ : Endpoint.Signs n) {a b c : Fin n}
    (hab : a<b) (hbc : b<c) :
    (Mapped (chainVal χ)).cupFirst 3 a b c ↔ Endpoint.StartState χ true 3 a b c := by
  change χ a b c = true ↔ Endpoint.StartState χ true 3 a b c
  exact ⟨fun h => (Endpoint.start_base χ true a b c).mpr ⟨hab,hbc,h⟩,
    fun h => ((Endpoint.start_base χ true a b c).mp h).2.2⟩

/-- Unlike the length-three triple states, pair states are never aliased.
These two identities isolate exactly what a later exclusion proof needs. -/
theorem chainVal_cap_pair {n : Nat} (χ : Endpoint.Signs n) (d : Nat) (a c : Fin n) :
    (Mapped (chainVal χ)).capPair d a c ↔ Endpoint.Ends χ false d a c := by
  change (stateVal (chainVal χ)).capPair d a c ↔ _
  rw [chainVal_states]; rfl

theorem chainVal_cup_pair {n : Nat} (χ : Endpoint.Signs n) (d : Nat) (a c : Fin n) :
    (Mapped (chainVal χ)).cupPair d a c ↔ Endpoint.Ends χ true d a c := by
  change (stateVal (chainVal χ)).cupPair d a c ↔ _
  rw [chainVal_states]; rfl

/-- Actual chains satisfy the pruned literal generator's propagation,
including its sign aliases. Exclusion is not assumed or proved here. -/
theorem chainVal_propagates {n A B : Nat} {χ : Endpoint.Signs n}
    (hχ : SignotopeConstraints n χ) :
    EndpointGuard.PrunedPropagation (signVal (chainVal χ)) A B (Mapped (chainVal χ)) := by
  unfold Mapped
  rw [chainVal_signs,chainVal_states]
  exact (guard_propagation (Endpoint.actual_propagates hχ A B)).to_pruned.baseAliases

theorem real_chainVal_propagates {n A B : Nat} (p : Fin n ↪ Plane)
    (hχ : SignotopeConstraints n (orientations p)) :
    EndpointGuard.PrunedPropagation (signVal (chainVal (orientations p))) A B
      (Mapped (chainVal (orientations p))) :=
  chainVal_propagates hχ

#print axioms chainVal_signs
#print axioms guard_propagation
#print axioms chainVal_states
#print axioms chainVal_cap_three
#print axioms chainVal_cup_three
#print axioms chainVal_cap_pair
#print axioms chainVal_cup_pair
#print axioms chainVal_propagates
#print axioms real_chainVal_propagates

end ES33.EndpointConcrete
