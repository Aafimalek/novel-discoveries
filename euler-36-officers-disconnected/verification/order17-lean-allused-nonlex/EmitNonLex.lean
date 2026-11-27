import EulerAllUsedNonLex
open LatinGap.PairEncoding EulerAllUsedDiagrams
def main : IO Unit := do
  for codes in published do
    IO.println s!"case {codes}"
    for row in archiveAllUsedNonLex codes do
      IO.println (String.intercalate " " (row.map toString) ++ " 0")
