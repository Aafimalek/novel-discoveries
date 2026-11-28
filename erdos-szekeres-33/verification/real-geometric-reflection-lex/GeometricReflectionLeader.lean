import GeometricReflection
import ReflectionLexTransport

namespace ES33.GeometricReflection

/-- A real residual realization with all exact residual target hypotheses. -/
def RealWitness (p : Fin 32 ↪ Plane) : Prop :=
  StrictMono (fun i => (p i).1) ∧ GeneralPosition p ∧ Residual32 (orientations p)

theorem reflected_witness {p : Fin 32 ↪ Plane} (hp : RealWitness p) :
    RealWitness (reflected p) :=
  ⟨reflected_increasing p hp.1, reflected_generalPosition p hp.2.1,
    reflected_residual32 p hp.2.2⟩

/-- Composition of the actual real orientation map and the checked
lex-leader theorem. The concrete orbit list/numbering is not asserted. -/
theorem real_lex_representative (reps : List (Triple 32)) :
    (∃ p : Fin 32 ↪ Plane, RealWitness p ∧
      ReflectionLex.Leader true (pairsWord reps (orientations p))) ↔
    ∃ p : Fin 32 ↪ Plane, RealWitness p :=
  ReflectionLex.exists_leader_representative RealWitness reflected
    (fun p => pairsWord reps (orientations p)) (fun _ => reflected_witness)
    (pairsWord_reflected reps)

#print axioms reflected_witness
#print axioms real_lex_representative

end ES33.GeometricReflection
