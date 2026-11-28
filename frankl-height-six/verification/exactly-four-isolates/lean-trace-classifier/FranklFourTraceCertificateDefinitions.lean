import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic

/- Finite certificate definitions verified with ordinary kernel reduction. -/
namespace FranklFourTraceCertificate

def mandatory : List Nat := [7, 11, 13, 14, 15]
def optional : List Nat := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12]

/-- The 11 mask bits choose optional traces, all five size-3/4 traces
being compulsory. Trace bits 0..3 are the labeled isolated points. -/
def profile (m : Nat) : List Nat :=
  mandatory ++ ((optional.zipIdx.filter (fun row => m.testBit row.2)).map Prod.fst)

def traceFrequency (m i : Nat) : Nat :=
  ((profile m).filter (fun t => t.testBit i)).length

def unionClosedB (m : Nat) : Bool :=
  (profile m).all (fun t => (profile m).all (fun u => (profile m).contains (t ||| u)))

def eligibleB (m : Nat) : Bool :=
  decide (2 * traceFrequency m 0 < (profile m).length) && unionClosedB m

/-- Any trace of a source-avoiding member must belong to this list,
since unioning with a source-containing member has a containing trace. -/
def safeAvoiding (m i j : Nat) : List Nat :=
  (List.range 16).filter (fun t =>
    !t.testBit i && !t.testBit j &&
      (profile m).all (fun u => (profile m).contains (t ||| u)))

def supportBits (m i j : Nat) : List Nat :=
  (List.range 4).filter (fun k => (safeAvoiding m i j).any (fun t => t.testBit k))

def surplusTest (m i j : Nat) : Prop :=
  (supportBits m i j).length + (profile m).length < traceFrequency m i + traceFrequency m j

instance (m i j : Nat) : Decidable (surplusTest m i j) := by
  unfold surplusTest
  infer_instance

structure Witness where
  i : Nat
  j : Nat
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat

abbrev StrictBitSubset (a b : Nat) : Prop :=
  a ≠ b ∧ a &&& b = a

/-- A checked witness includes the strict incidence advantage, the
four-member containing trace chain, and safe support below its bottom. -/
def WitnessSpec (m : Nat) (w : Witness) : Prop :=
  w.i < w.j ∧ w.j < 4 ∧ surplusTest m w.i w.j ∧
  w.c0 ∈ profile m ∧ w.c1 ∈ profile m ∧ w.c2 ∈ profile m ∧ w.c3 ∈ profile m ∧
  StrictBitSubset w.c0 w.c1 ∧ StrictBitSubset w.c1 w.c2 ∧ StrictBitSubset w.c2 w.c3 ∧
  (safeAvoiding m w.i w.j).all (fun t => (t &&& w.c0) == t) = true

instance (m : Nat) (w : Witness) : Decidable (WitnessSpec m w) := by
  unfold WitnessSpec
  infer_instance

def validWitness (m : Nat) (w : Witness) : Bool :=
  decide (WitnessSpec m w)

theorem witness_spec_of_valid {m : Nat} {w : Witness}
    (h : validWitness m w = true) : WitnessSpec m w :=
  of_decide_eq_true h

theorem eligibleB_spec {m : Nat} (h : eligibleB m = true) :
    2 * traceFrequency m 0 < (profile m).length ∧
      ∀ t ∈ profile m, ∀ u ∈ profile m, (t ||| u) ∈ profile m := by
  have hp := Bool.and_eq_true_iff.mp h
  refine ⟨of_decide_eq_true hp.1,?_⟩
  intro t ht u hu
  have houter := List.all_eq_true.mp hp.2 t ht
  have hinner := List.all_eq_true.mp houter u hu
  simpa using hinner

/-- The one named survivor is the full trace cube except trace {0}. -/
theorem survivor_profile :
    profile 2045 = [7,11,13,14,15,0,2,3,4,5,6,8,9,10,12] ∧
    eligibleB 2045 = true ∧ (profile 2045).length = 15 ∧
    traceFrequency 2045 0 = 7 ∧ traceFrequency 2045 1 = 8 ∧
    traceFrequency 2045 2 = 8 ∧ traceFrequency 2045 3 = 8 := by
  decide

def allPairs : List (Nat × Nat) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

private theorem allPairs_complete (i j : Nat) (hij : i < j) (hj : j < 4) :
    (i,j) ∈ allPairs := by
  have h : i = 0 ∧ j = 1 ∨ i = 0 ∧ j = 2 ∨ i = 0 ∧ j = 3 ∨
      i = 1 ∧ j = 2 ∨ i = 1 ∧ j = 3 ∨ i = 2 ∧ j = 3 := by omega
  simpa [allPairs] using h

theorem survivor_has_no_surplus_pair (i j : Nat) (hij : i < j) (hj : j < 4) :
    ¬ surplusTest 2045 i j := by
  have hAll : allPairs.all (fun p => !decide (surplusTest 2045 p.1 p.2)) = true := by
    decide
  have hpair := List.all_eq_true.mp hAll (i,j) (allPairs_complete i j hij hj)
  simpa using hpair

theorem survivor_has_no_valid_witness (w : Witness) :
    validWitness 2045 w ≠ true := by
  intro h
  have hh := witness_spec_of_valid h
  exact survivor_has_no_surplus_pair w.i w.j hh.1 hh.2.1 hh.2.2.1

#print axioms witness_spec_of_valid
#print axioms eligibleB_spec
#print axioms survivor_profile
#print axioms survivor_has_no_valid_witness
end FranklFourTraceCertificate
