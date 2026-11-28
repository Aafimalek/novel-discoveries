# Lean-checked actual diagonal-branch anchors

This is a source-only delta importing the previously checked
DiagonalBranchHeadDraft module. The clean source (its name preserves
the compiled import) and an independent typed import audit both exited
zero on pinned Lean 4.36.0 (611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9)
with Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842. All six audited
endpoints depend only on propext, Classical.choice, Quot.sound.
Both strict runs used -DwarningAsError=true and emitted no warnings.
This release replaces deprecated dependent-if names and omits unused
Fintype section assumptions in local support lemmas. The original
checked snapshot is unchanged. No placeholders or native evaluation
are used.

- Labels.initialSegments_le_branchPosition counts prefix and initial rail
  labels at or before a point in an actual Ranking.
- Labels.twoAnchor_branchPositionSum proves the lower rank sum for the
  last-low label from each arm, including a common-prefix fallback on
  either/both empty rail prefixes. Labels.repeated_y_anchor_baseline
  supplies the mirror of the earlier repeated-X case.
- Labels.exists_fixed_anchors selects actual anchors from the chosen
  low prefixes, outside the quantification over rankings.
- Labels.exists_anchors_frequency_heads_le applies the checked
  joint comparison frequency implication using these derived anchors.
  Labels.heads_not_both_high uses exact integer comparisons to rule out
  two highs when given their low prefixes and a low terminal prefix point.

The dependency is the verified diagonal-head package plus its existing
joint-ranking prerequisites. There is no product factorization of cuts
and rankings. The final balanced-pair theorem still requires the common
prefix induction, selection of low/high boundaries, and the all-low or
one-high exclusions. It is not claimed by this package.

For serial replay in an overlay, give LEAN_BIN and LEAN_PATH (prior
checked objects, including DiagonalBranchHeadDraft, and pinned Mathlib).
Run ./replay.sh. The archived original object hashes document the clean
run; the objects themselves are not shipped.
