import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace TwoByThreeReplay

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

/-- Labels 0 through 6 are b,x,X,y,Y,Z,a. The rows are the ten interleavings. -/
def branchRank (p : Fin 10) (u : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 4, 5, 6], ![0, 1, 3, 2, 4, 5, 6], ![0, 1, 4, 2, 3, 5, 6], ![0, 1, 5, 2, 3, 4, 6], ![0, 2, 3, 1, 4, 5, 6], ![0, 2, 4, 1, 3, 5, 6], ![0, 2, 5, 1, 3, 4, 6], ![0, 3, 4, 1, 2, 5, 6], ![0, 3, 5, 1, 2, 4, 6], ![0, 4, 5, 1, 2, 3, 6]] p u

def rank (p : Fin 10) (j u : Fin 7) : ℕ :=
  if u = 6 then j.val else branchRank p u + if j.val ≤ branchRank p u then 1 else 0

/-- Integer count of a forward comparison in one uniform cutoff component. -/
def component (p : Fin 10) (k u v : Fin 7) : ℕ :=
  if u = 6 then
    if v = 6 then 0 else min (k.val + 1) (branchRank p v + 1)
  else if v = 6 then
    k.val + 1 - min (k.val + 1) (branchRank p u + 1)
  else if branchRank p u < branchRank p v then k.val + 1 else 0

abbrev Term := ℕ × Fin 7 × Fin 7
abbrev Certificate := List Term × ℕ

def cert (r : Fin 25) : Certificate :=
  ![([(2, 2, 6), (3, 5, 6)], 100),
   ([(1, 2, 6), (1, 4, 6)], 40),
   ([(30, 6, 1), (60, 0, 6), (5, 1, 4), (3, 1, 5), (10, 1, 3)], 2340),
   ([(4, 6, 3), (6, 1, 6), (1, 3, 2)], 220),
   ([(1, 1, 3), (7, 3, 6)], 160),
   ([(2, 6, 3), (4, 0, 6), (1, 3, 1)], 152),
   ([(20, 6, 1), (5, 1, 4), (3, 1, 5), (30, 3, 6)], 1160),
   ([(7, 1, 6), (1, 3, 1)], 160),
   ([(6, 6, 3), (12, 0, 6), (1, 3, 2), (2, 3, 1)], 456),
   ([(1, 4, 6)], 20),
   ([(7, 4, 6), (1, 1, 3)], 160),
   ([(7, 4, 6), (1, 1, 4)], 160),
   ([(4, 4, 1), (10, 6, 4), (15, 3, 6)], 580),
   ([(2, 4, 6), (1, 1, 6)], 60),
   ([(2, 6, 2), (6, 6, 3), (15, 1, 6)], 460),
   ([(1, 2, 6)], 20),
   ([(2, 2, 6), (1, 3, 6)], 60),
   ([(7, 2, 6), (1, 3, 2)], 160),
   ([(7, 5, 6), (1, 1, 3)], 160),
   ([(7, 2, 6), (1, 3, 1)], 160),
   ([(7, 5, 6), (1, 1, 4)], 160),
   ([(3, 4, 2), (5, 4, 1), (20, 6, 4), (30, 3, 6)], 1160),
   ([(7, 5, 6), (1, 1, 5)], 160),
   ([(1, 5, 6)], 20),
   ([(3, 5, 6), (1, 1, 6)], 80)] r

def coeff (t : Term) := t.1
def start (t : Term) := t.2.1
def finish (t : Term) := t.2.2
def isBase (t : Term) : Bool := t.2 == (0,6)
def componentForm (terms : List Term) (p : Fin 10) (k : Fin 7) : ℕ :=
  (terms.map fun t => coeff t * component p k (start t) (finish t)).sum
def baseCoeff (terms : List Term) : ℕ :=
  (terms.map fun t => if isBase t then coeff t else 0).sum
def otherCoeff (terms : List Term) : ℕ :=
  (terms.map fun t => if isBase t then 0 else coeff t).sum

def fits (p : Fin 10) (j : Fin 6) (terms : List Term) : Bool :=
  terms.all (fun t => decide (rank p ⟨j.val+1,by omega⟩ (start t) <
    rank p ⟨j.val+1,by omega⟩ (finish t)))

/-- Checks all 1,750 integer inequalities without trusting the exploratory solver. -/
theorem replay_component_bound (r : Fin 25) :
    ∀ (p : Fin 10) (k : Fin 7),
      30 * componentForm (cert r).1 p k ≤ (cert r).2 * (k.val + 1) := by
  fin_cases r <;> decide

/-- The thresholds from the strict forward comparisons and P(a<b) ≤ 7/30. -/
theorem replay_budget :
    ∀ r : Fin 25, (cert r).2 = 23 * baseCoeff (cert r).1 + 20 * otherCoeff (cert r).1 ∧
      otherCoeff (cert r).1 > 0 := by decide

/-- Classifies the 60 majority orders by their applicable certificate; the
non-initial positions of a are covered without charging b<a. -/
theorem replay_orientation_coverage :
    ∀ p : Fin 10, ∀ j : Fin 6, ∃ r : Fin 25,
      fits p j (cert r).1 = true ∧ (j = 0 ∨ baseCoeff (cert r).1 = 0) := by
  decide

def quarterX : List Term := [(12,0,6),(6,6,1),(2,1,3),(1,1,4)]
def quarterY : List Term := [(12,0,6),(6,6,3),(2,3,1),(1,3,2)]

/-- Additional early-order witness for the quarter bound with x<Z. -/
theorem replay_quarter_X :
    ∀ p : Fin 10, ∀ k : Fin 7, branchRank p 1 < branchRank p 5 →
      componentForm quarterX p k ≤ 15 * (k.val + 1) := by decide

/-- The early y-majority orientation only uses the short, two-element arm. -/
theorem replay_quarter_Y :
    ∀ p : Fin 10, ∀ k : Fin 7,
      componentForm quarterY p k ≤ 15 * (k.val + 1) := by decide

theorem replay_quarter_early_coverage :
    ∀ p : Fin 10, fits p 0 quarterX = true ∨ fits p 0 quarterY = true := by decide

#print axioms replay_component_bound
#print axioms replay_budget
#print axioms replay_orientation_coverage
#print axioms replay_quarter_X
#print axioms replay_quarter_Y

end TwoByThreeReplay
