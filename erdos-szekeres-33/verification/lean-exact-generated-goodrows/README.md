# Checked ES33 endpoint constructor exhaustiveness and coverage lemmas

Strict Lean 4.36.0, one worker, warnings as errors, 2250 MB Lean limit,
2310000 KiB observed-RSS cap, overlay TMPDIR: both modules exited zero.
Measured 1.619 s and 1.157 s. Axiom reports contain only the standard
`propext`, `Classical.choice`, and `Quot.sound` (or a subset).

- `actual_goodRows n K A B (hA : 2 ≤ A) (hB : 2 ≤ B)` proves
  `GoodRows n K A B` for the exact executable typed generator.
  `target32_goodRows` has no size hypotheses: `GoodRows 32 7 7 6`.
- The coverage module proves sign, pair, and triple-state key membership
  under the stated index/length guards, and verifies all projection and
  extension span inequalities needed for the subsequent coverage proof.
  In particular length-three states use sign keys.
- Generator-level `VerificationGoals.covered` is not proved here.
  Real-state propagation and exclusion, external DIMACS equality, and
  target UNSAT are also not claimed.

Replay using the existing verified prerequisite objects whose hashes the two
JSON receipts list. The serial runner checks the original bridge dependency
receipts and pins the Lean executable. In the original overlay, preserve the
objects already there; for a fresh replay directory, place these sources and
the runner in it, create `out/` and `tmp/`, and run
`python run_stage.py ActualGoodRows 80`, then
`python run_stage.py CoverageInequalities 80`.
