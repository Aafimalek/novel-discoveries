import EulerArchivedOverlaps
open LatinGap.PairEncoding
def main : IO Unit := do
  for s in [OverlapCase.q2, .double, .one, .zero] do
    IO.println s!"{repr s}"
    for c in archivedOverlapBlock s do IO.println s!"{c}"
