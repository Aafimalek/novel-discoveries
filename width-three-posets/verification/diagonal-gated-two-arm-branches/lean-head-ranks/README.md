# Lean-checked diagonal-gated head ranks in actual finite-poset rankings

Pinned Lean 4.36.0 (commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9) and
Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842 checked both sources and
a separate import-and-type audit in the supplied overlay run. Only the
usual axioms were reported: propext and Quot.sound for the self-contained
arithmetic, and additionally Classical.choice for the ranking statements.
The filename DiagonalBranchHeadDraft.lean preserves the compiled module
name. No placeholders or native computation are used.

- DiagonalRankArithmetic: exact max/imbalance arithmetic for selecting
  a fixed anchor pair, one-early-head rank addition, and the gate cap.
- Labels.x_branchPosition_gate and Labels.y_branchPosition_gate: a single
  directional gate bounds branch rank even when the other arm is short;
  an opposing point past the offset would force the gate endpoint to exist.
  No new pairwise relations besides the labeled rails and supplied gate
  are assumed.
- Labels.head_rankSum_upper: the earlier actual head sees only the two low
  prefixes. Together with the directional bounds this bounds the total
  branch rank of the two heads by
  2*h + 2*(i+j) + 2 + max(d,e) + |i-j|.
- Labels.repeated_x_anchor_baseline: an actual lower bound for the anchor
  when an X predecessor is repeated in the imbalanced case.
- Labels.frequency_heads_le: the branch-order sums discharge the universal
  rank hypothesis of the previously checked joint-frequency endpoint when
  the fixed-anchor lower bound and max(d,e)+2 <= 2*h are supplied.

This package checks the actual branch-order/frequency implication. It does
not yet formalize the mirror and two-distinct-lows anchor cases or the
assembled no-balance contradiction, and does not prove the full width-three
1/3–2/3 conjecture. The corrected manuscript copy is a separate written
structural argument, not a Lean audit of every claim it contains. No cut /
branch-order product factorization is used.

## Replay

Provide the pinned LEAN_BIN and LEAN_PATH with the precompiled
JointBranchOrderDraft and its prerequisites. These are included in the
previous checked joint-ranking source package (BranchSwap, BranchOrder,
MultiRankStep, JointCapDraft, AntitonePrefixDraft, ConditionalBinListDraft,
and JointBranchOrderDraft). Use a writable overlay copy and run
./replay.sh serially. Checked logs are under logs/. Object hashes record
the original run (the source-only package does not ship the objects).
