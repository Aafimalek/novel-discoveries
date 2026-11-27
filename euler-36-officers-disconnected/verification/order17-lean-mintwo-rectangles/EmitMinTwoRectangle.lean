import EulerMinTwoCandidateRectangle
open LatinGap.PairEncoding
def main : IO Unit := for row in archiveMinTwoCandidateRectangleBlock do
  IO.println s!"{row}"
