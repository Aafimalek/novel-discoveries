/- Static side numbering specification. Executable counts plus exact
proof goals, not asserted equalities. No compiler has run. -/
import OrientationRank

namespace ES33.EndpointConcrete.SideRankSpec

open ES33.Numbering
open OrientationRank (before after gtLabels firstWeight)

def pairWeight {n : Nat} (L : Nat) (a c : Fin n) : Nat :=
  min L (width2 a c) - 1

def tripleWeight {n : Nat} (f : Side) (L : Nat) (a b c : Fin n) : Nat :=
  min L (width3 f a b c) - 3

def firstPairWeight {n : Nat} (L : Nat) (a : Fin n) : Nat :=
  ((after a).map (pairWeight L a)).sum

def secondTripleWeight {n : Nat} (f : Side) (L : Nat) (a b : Fin n) : Nat :=
  ((after b).map (tripleWeight f L a b)).sum

def firstTripleWeight {n : Nat} (f : Side) (L : Nat) (a : Fin n) : Nat :=
  ((after a).map (secondTripleWeight f L a)).sum

def totalPairs (n L : Nat) : Nat :=
  ((List.finRange n).map (firstPairWeight L)).sum

def totalTriples (n : Nat) (f : Side) (L : Nat) : Nat :=
  ((List.finRange n).map (firstTripleWeight f L)).sum

def totalSigns (n : Nat) : Nat := ((List.finRange n).map firstWeight).sum

def sideBase (n A : Nat) (f : Side) : Nat :=
  match f with
  | .cap => totalSigns n
  | .cup => totalSigns n + totalPairs n A + totalTriples n .cap A

def sideLimit (A B : Nat) : Side → Nat
  | .cap => A
  | .cup => B

def pairPrefix {n : Nat} (L : Nat) (a c : Fin n) : Nat :=
  ((before a).map (firstPairWeight L)).sum +
    ((gtLabels a (before c)).map (pairWeight L a)).sum

def triplePrefix {n : Nat} (f : Side) (L : Nat) (a b c : Fin n) : Nat :=
  ((before a).map (firstTripleWeight f L)).sum +
    ((gtLabels a (before b)).map (secondTripleWeight f L a)).sum +
    ((gtLabels b (before c)).map (tripleWeight f L a b)).sum

def pairId {n : Nat} (A B : Nat) (f : Side) (d : Nat) (a c : Fin n) : Nat :=
  sideBase n A f + pairPrefix (sideLimit A B f) a c + (d-2) + 1

def tripleId {n : Nat} (A B : Nat) (f : Side) (d : Nat) (a b c : Fin n) : Nat :=
  let L := sideLimit A B f
  sideBase n A f + totalPairs n L + triplePrefix f L a b c + (d-4) + 1

/-- A length-three state is a signed orientation alias, not a side ID. -/
def stateWord {n : Nat} (A B : Nat) (f : Side) (d : Nat) (a b c : Fin n) : Int :=
  if d=3 then
    let s : Int := OrientationRank.rank a b c
    match f with
    | .cap => -s
    | .cup => s
  else tripleId A B f d a b c

/-- Exact side hinge, stated and deliberately not assumed or asserted. -/
def PairIdsCorrect (n A B : Nat) : Prop :=
  ∀ (f : Side) (d : Nat) (a c : Fin n), a<c → 2≤d →
    d≤min (sideLimit A B f) (width2 a c) →
    (dictionary n A B).idxOf (pairKey f d a c) + 1 = pairId A B f d a c

/-- Exact length>=4 side hinge, separate from the length-three alias. -/
def TripleIdsCorrect (n A B : Nat) : Prop :=
  ∀ (f : Side) (d : Nat) (a b c : Fin n), a<b → b<c → 4≤d →
    d≤min (sideLimit A B f) (width3 f a b c) →
    (dictionary n A B).idxOf (stateKey f d a b c) + 1 = tripleId A B f d a b c

end ES33.EndpointConcrete.SideRankSpec
