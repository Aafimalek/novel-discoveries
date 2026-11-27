import RotationData

namespace CertifiedG449Rotation

open G449OrbitArithmetic

def publishedPairs : List (Nat × Nat) :=
  allPublishedEdges.map fun e => (e.a,e.b)

def orientedPairs : List (Nat × Nat) :=
  (List.range 449).flatMap fun a => (upperNeighbors a).map fun b => (a,b)

def canonicalPair (a b : Nat) : Nat × Nat :=
  if a ≤ b then (a,b) else (b,a)

def Adj (a b : Nat) : Prop := canonicalPair a b ∈ publishedPairs

def adjB (a b : Nat) : Bool :=
  if a ≤ b then (upperNeighbors a).contains b
  else (upperNeighbors b).contains a

def edgeActionValid (e : Edge) : Bool :=
  adjB (rot e.a) (rot e.b) && adjB (inv e.a) (inv e.b)

def permOK (k : Nat) : Bool :=
  decide (rot k < 449) && decide (inv k < 449) &&
    (inv (rot k) == k) && (rot (inv k) == k)

def geomOK (k : Nat) : Bool :=
  (List.range 12).all fun i =>
    (vertices (rot k)).coeffs.getD i 0 ==
    spin (fun j => (vertices k).coeffs.getD j 0) i

def centerMembershipOK (k : Nat) : Bool := adjB center k == ring.contains k

def cyclicOK (i : Nat) : Bool :=
  rot (ring.getD i 0) == ring.getD ((i+1)%7) 0

def independenceOK : Bool :=
  ring.all fun a => ring.all fun b => decide (a=b) || !(adjB a b)

end CertifiedG449Rotation
