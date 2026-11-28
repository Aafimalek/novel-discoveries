# Checked four-drop certificate at a quad anchor

Pinned ordinary Lean 4.36, strict warnings as errors, one worker,
2500 MB, overlay temporary storage. The two new modules replay
against previously checked local dependencies.

For a weak minimal NoStrictMajority family with exactly four isolates
and all source deficits at most two, if p lies in a quad and q outside
it also has exact deficit two, the pair anchor block is ordinary and
the disjoint linked mate groups give four deletions. If q is in a
quad this is 2+2; otherwise q lies in two incident triples and it is
2+1+1. The checked theorem
`FranklForcingFiber.quad_and_outside_deficitTwo_impossible`
applies the conditional four-drop contradiction to that certificate.
Separate endpoint `quad_and_outside_deficitTwo_four_drops` constructs
the geometry without assuming exactly four isolates.

This excludes only quads with another outside deficit-two source.
The unique-quad / otherwise deficit-at-most-one branch and the
overlapping-triples-only case remain separate.
