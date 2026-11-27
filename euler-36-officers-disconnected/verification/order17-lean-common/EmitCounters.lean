import EulerNumberedCounters
open LatinGap.PairEncoding
open LatinGap

def main : IO Unit := do
  let input := archiveProjectionCountBlock ++ ([0,1,2,3] : List Coord).flatMap archiveDegreeExcessCountBlock
  IO.println (reprStr input)
