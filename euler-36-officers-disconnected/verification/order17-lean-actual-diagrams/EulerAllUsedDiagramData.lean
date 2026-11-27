import Init

namespace EulerAllUsedDiagrams

def indices : List Nat := [0,1,2,3]
def patterns : List (List Nat) := [[1,1,1],[1,1,2],[1,2,1],[1,2,2],[1,2,3]]

def fourChoices (xs : List α) : List (List α) :=
  xs.flatMap fun a => xs.flatMap fun b => xs.flatMap fun c => xs.map fun d => [a,b,c,d]

def allPermutations : List (List Nat) :=
  (fourChoices indices).filter fun a => a.eraseDups.length == 4

def value (m : List (List Nat)) (i j : Nat) : Nat := (m.getD i []).getD j 0

def ofColumns (cols : List (List Nat)) : List (List Nat) :=
  indices.map fun i => indices.map fun j =>
    if i == j then 0 else value cols j (if i < j then i else i-1)

def oneOverlap (m : List (List Nat)) : Bool :=
  indices.all fun i => indices.all fun j => if i < j then
    (indices.filter fun k => value m i k == value m j k).length ≤ 1 else true

def normalize (m : List (List Nat)) (p : List Nat) : List Nat :=
  let entry (i j : Nat) := value m (p.getD i 0) (p.getD j 0)
  let ranks := indices.map fun j =>
    ((indices.map fun i => entry i j).filter fun v => v != 0).eraseDups
  indices.map fun i => (indices.map fun j =>
    if entry i j == 0 then 0 else ((ranks.getD j []).idxOf (entry i j)) + 1)
      |>.foldl (fun a v => a * 10 + v) 0

def canonical (m : List (List Nat)) : List Nat :=
  (allPermutations.map (normalize m)).foldl
    (fun a b => if compare a b == .gt then b else a) [9999]

def insertCase (a : List Nat) : List (List Nat) → List (List Nat)
  | [] => [a]
  | b::bs =>
    match compare a b with
    | .lt => a::b::bs
    | .eq => b::bs
    | .gt => b :: insertCase a bs

def cases : List (List Nat) :=
  let raw := (fourChoices patterns).map ofColumns
  ((raw.filter oneOverlap).map canonical).foldl (fun a b => insertCase b a) []

def published : List (List Nat) :=
 [[111,1012,1103,1220],[111,1012,1103,2220],[111,1012,1201,1120],
  [111,1012,1201,1320],[111,1012,1201,2120],[111,1012,1201,2320],
  [111,1012,1203,1320],[111,1012,1203,2120],[111,1012,1203,2320],
  [111,1012,2201,1220],[111,1012,2201,1320],[111,1012,2201,3120],
  [111,1012,2201,3320],[111,1012,2203,2320],[111,1012,2203,3310],
  [111,1012,2203,3320],[111,1022,2203,3330]]

end EulerAllUsedDiagrams
