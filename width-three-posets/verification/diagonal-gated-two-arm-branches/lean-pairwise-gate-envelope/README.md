# Lean-checked pairwise local gate envelope arithmetic

This standalone module imports Lean Init only. Pinned Lean 4.36.0
(commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9) checked this module
and the independent typed fresh import with one worker, -M600, and
-DwarningAsError=true. The three endpoints depend only on
propext and Quot.sound:

- pairwise_envelope_rank_le: the late-rank budgets A and B choose
  transposed integer weights B and A.
- pairwise_envelope_weights_iff: exact existence of nonzero weights
  that meet both abstract late-head bounds. This sharpness is for
  the envelope inequalities, not for actual poset realizability.
- pairwise_budget_of_one_small: one small local increment suffices.

The full pairwise-gate poset theorem and the concrete 24-element
witness have not been checked in Lean by this package. The supplied
witness is a separate written argument, not a compiler receipt.
The object hashes document the original clean run; objects themselves
are not shipped. No placeholders or native evaluation are used.

For replay from a writable overlay, provide LEAN_BIN and an absolute
shared LOCK_PATH agreed with other workers. Run ./replay.sh serially.
No Mathlib or previous project imports are needed.

Written companion: [pairwise gate budgets](pairwise-gates.md) and the
[finite realization](explicit-finite-realization.md).
