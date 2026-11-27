# Two-by-three arm cutoff certificates

These files certify finite inequalities for the antitone cutoff-histogram model used in the width-three poset project. They do not yet formalize the reduction from arbitrary actual poset rankings of this branch shape to the enumeration.

- `lean/TwoByThreeReplay.lean`: ten branch interleavings; 25 certificate rows; 1,750 per-component inequalities; exhaustive coverage of 60 candidate majority orientations after the root; two direct early-case quarter-threshold certificates.
- `lean/TwoByThreeMixtures.lean`: lifts the inequalities to arbitrary nonnegative integer cutoff weights. The first theorem rules out all listed strict majority orientations when the root-first comparison count is at most 7/30 of the total. The second gives the quarter bound when the weight support obeys `x < Z`.
- `lean/TwoByThreeObstruction.lean`: independently verifies a component mixture of mass 62, root-first count 15, and no balanced distinct pair. This is a counterexample only in the cutoff-histogram model.

All checks ran with plain Lean 4.36.0 and Mathlib. The audit permits only propext, Classical.choice, and Quot.sound; the obstruction uses only propext. Nothing requires an external solver during Lean checking. There are no compiled artifacts here.

Build `TwoByThreeReplay.lean` first, then `TwoByThreeMixtures.lean` and `TwoByThreeObstruction.lean` (both import `TwoByThreeReplay`). To regenerate the first two files, run `python3 gen.py` and `python3 gen-mix.py` in `generator/`. The original certificate data is `generator/cert.json`.
