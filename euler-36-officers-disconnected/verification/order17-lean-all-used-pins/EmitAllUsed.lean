import EulerAllUsedPinProfile
open LatinGap.PairEncoding EulerAllUsedDiagrams
def main : IO Unit := do
  IO.println s!"{archiveAllUsedAnchorUnits}"
  for case in published do
    IO.println s!"{case}"
    IO.println s!"{archiveAllUsedPinProfile case}"
