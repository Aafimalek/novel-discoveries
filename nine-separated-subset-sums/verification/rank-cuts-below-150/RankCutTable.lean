import Init.Data.List.Basic

namespace NineGap

/-- Four-element cube vertices in lexicographic order, using coordinates 0–8.
A selected vertex indexed by a<b<c<d contributes 8-d distinct five-sets
whose lex-first four-subset is that vertex. -/
def fourSetShadowMultiplicities : List Nat :=
  (List.range 6).flatMap fun a =>
    ((List.range (6-a)).map (· + a + 1)).flatMap fun b =>
      ((List.range (7-b)).map (· + b + 1)).flatMap fun c =>
        (List.range (8-c)).map fun t => 8 - (t + c + 1)

/-- For a prefix containing every set of size at most three and only
part of the fourth layer: remaining four-sets plus the fifth-layer shadow. -/
def fourthLayerBoundary (k : Nat) : Nat :=
  let t := k - 130
  (126 - t) + (fourSetShadowMultiplicities.take t).foldl (· + ·) 0

def cuts : List Nat := [158, 159, 161, 162, 168, 169, 171, 172,
                       193, 194, 196, 197, 203, 204, 206, 207]

theorem fourSetCount : fourSetShadowMultiplicities.length = 126 := by rfl

theorem cutBoundaries : cuts.map fourthLayerBoundary = List.replicate 16 148 := by rfl

def forbidden (k m : Nat) : Bool :=
  let reflected := 513 - m - k
  let l := min k reflected
  257 - m ≤ l && l ≤ (504 - m) / 2

theorem saturated149Predecessors :
    cuts.all (fun k => forbidden k 149 && forbidden (k - 1) 149) = true := by rfl

theorem penultimate148Band :
    cuts.all (fun k =>
      let l := min k (513 - 148 - k)
      109 ≤ l && l ≤ 177) = true := by rfl

#print axioms fourSetCount
#print axioms cutBoundaries
#print axioms saturated149Predecessors
#print axioms penultimate148Band

end NineGap
