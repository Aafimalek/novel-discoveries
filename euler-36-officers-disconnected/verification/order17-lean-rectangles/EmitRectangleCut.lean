import EulerRectangleCut

open LatinGap LatinGap.PairEncoding

def main : IO Unit := do
  for i in (List.ofFn (fun x : Coord => x)) do
    for j in (List.ofFn (fun x : Coord => x)) do
      if h : i < j then
        for a in (List.ofFn (fun x : Fin 6 => x)) do
          for b in (List.ofFn (fun x : Fin 6 => x)) do
            let clause := rectangleCut ⟨i,j,h,a,b⟩ (1 : Fin 6) 1
            IO.println (String.intercalate " " (clause.map toString) ++ " 0")
