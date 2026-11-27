import EulerDegreeThreshold

open LatinGap LatinGap.PairEncoding

def main : IO Unit := do
  for g in (List.ofFn (fun i : Coord => i)) do
    for a in (List.ofFn (fun i : Fin 6 => i)) do
      for clause in degreeBlock 2 g a do
        IO.println (String.intercalate " " (clause.map toString) ++ " 0")
