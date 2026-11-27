import TwoByThreeReplay

namespace TwoByThreeReplay

/-- Three nonzero cutoff weights: one on (0,1), ten on (0,3), four on (9,4). -/
def obstructionCount (u v : Fin 7) : ℕ :=
  component 0 1 u v + 10 * component 0 3 u v + 4 * component 9 4 u v

def obstructionMass : ℕ := 2 + 10 * 4 + 4 * 5

/-- An abstract monotone cutoff mixture at 15/62 has no balanced pair.
This is not a counterexample about actual posets. -/
theorem checked_obstruction :
    obstructionMass = 62 ∧ obstructionCount 6 0 = 15 ∧
      (∀ u v : Fin 7, u ≠ v →
        3 * obstructionCount u v < obstructionMass ∨
        2 * obstructionMass < 3 * obstructionCount u v) := by decide

#print axioms checked_obstruction
end TwoByThreeReplay
