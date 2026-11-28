# Partial strict Lean replay: exact cycle and saturation lemmas

Pinned ordinary Lean 4.36.0, commit
611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, warning as error, one worker,
2500 MB, and overlay temporary storage. Draft sources were not edited.

1. `FranklTwoMateCollapse`: exit 0, elapsed 39.784 s. Proves the
   retraction has exactly its specified nontrivial fibers and equal
   images of nonloop disjoint second mate edges force crossing.
2. `FranklSaturatedFourTriples`: exit 0, elapsed 36.165 s. Proves
   four pairwise-meeting triples in a triple-degree-at-most-two pair
   design are saturated and disjoint from every outside triple.
3. `FranklActualAlternatingCycle`: stopped to honor the wave time
   limit, with exit 130, no diagnostic and no compiled object.
   It is not part of the checked partial endpoint.

All three printed audits in the two successful modules reported exactly
`[propext, Classical.choice, Quot.sound]`. No warning, sorry or native
evaluation in these checked artifacts. The separate noncycle batch
was not run. See the two genuine module logs and checked-only manifest.
