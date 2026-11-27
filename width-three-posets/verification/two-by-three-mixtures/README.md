# Two-by-three arm cutoff certificates

These files certify finite inequalities for the antitone cutoff-histogram model used in the width-three poset project. They do not yet formalize the reduction from arbitrary actual poset rankings of this branch shape to the enumeration.

- `lean/TwoByThreeReplay.lean`: ten branch interleavings; 25 certificate rows; 1,750 per-component inequalities; exhaustive coverage of 60 candidate majority orientations after the root; two direct early-case quarter-threshold certificates.
- `lean/TwoByThreeMixtures.lean`: lifts the inequalities to arbitrary nonnegative integer cutoff weights. The first theorem rules out all listed strict majority orientations when the root-first comparison count is at most 7/30 of the total. The second gives the quarter bound when the weight support obeys `x < Z`.
- `lean/TwoByThreeObstruction.lean`: independently verifies a component mixture of mass 62, root-first count 15, and no balanced distinct pair. This is a counterexample only in the cutoff-histogram model.

All checks ran with plain Lean 4.36.0 and Mathlib. The audit permits only propext, Classical.choice, and Quot.sound; the obstruction uses only propext. Nothing requires an external solver during Lean checking. There are no compiled artifacts here.

Build `TwoByThreeReplay.lean` first, then `TwoByThreeMixtures.lean` and `TwoByThreeObstruction.lean` (both import `TwoByThreeReplay`). To regenerate the first two files, run `python3 gen.py` and `python3 gen-mix.py` in `generator/`. The original certificate data is `generator/cert.json`.

## Actual rankings to histograms

The added [TwoByThreeRankingBridge.lean](lean/TwoByThreeRankingBridge.lean) verifies that actual rankings with the assumed exclusive upset give an antitone 10-by-7 histogram. It checks the exact total, all pair counts on the seven labels, and the relevant histogram support condition when x<Z. Build after `TwoByThreeReplay` with the existing checked `BranchOrder` on the module path. The [audit](logs/bridge1.log) contains a harmless unused-variable lint and only the three standard axioms.

Still missing for an end-to-end Lean balanced-pair theorem: the generalization of the antitone histogram-to-cutoff decomposition to these 10-by-7 weights, and the classification of a strict-majority ordering under the assumption of no balanced pair. The checked obstruction concerns histograms, not actual posets.

**Update:** The missing links are now checked in the [separate end-to-end 2×3 ranking theorem](../two-by-three-balanced). This directory preserves the earlier stand-alone audit; use the new directory’s build instructions for the complete restricted theorem.
