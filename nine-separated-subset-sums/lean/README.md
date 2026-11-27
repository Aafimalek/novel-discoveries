# Lean verification of the real-to-integer reduction

The full real argument is checked in [`RealReduction.lean`](NineSeparatedSubsetSums/RealReduction.lean). The theorem `real_counterexample_reduces_to_integer` proves that nine positive real weights with pairwise unit-separated subset sums and largest weight below 149 yield nine positive integer weights, largest weight exactly 148, whose subset sums are all distinct.

The proof sorts the real scores, uses the nine-dimensional cube cut to force the first critical block, checks the rounding along its projected coordinate paths, then uses reflection and translates every hypothetical collision into the central block. The corollary `separated_nine_at_least_149_of_integer_exclusion` proves the lower bound **conditional on the explicit finite integer exclusion in its statement**. Both theorems compile with Lean 4.36.0 and report only `propext`, `Classical.choice`, and `Quot.sound`.

**The remaining Lean task is the integer exclusion.** `integerMomentBoundOfDistinctSublists` proves the moment bound 87381, and `noDistinctSublistsMax148SecondLe99` proves an integer partial exclusion up to second-largest weight 99. We independently completed the [C++ exhaustive search](../verification/integer-search.md) at exact maximum 148 with no witness, but it is not a Lean certificate for second-largest weights 100–147. The lower bound is not yet end-to-end verified in Lean, and the exact real optimum remains in [149, 161].

From this directory, run `lake build` with the pinned toolchain. The axiom audits are printed in each module. See the [written paper](../paper/nine-separated-subset-sums.pdf) for the result using the published integer optimum.

The exact integer search now has a checked correctness interface. `integer_max148_forces_search_true` proves any candidate would make the explicit max-148 search return true. The mask, pruning, and input conversion are formalized. The search Boolean has **not** been shown false in Lean; the separate checked two-weight mask lemma is a route to a smaller certificate, not yet integrated into a complete evaluation.

`IntegerShards` splits the exact max-148 check by the second-largest integer weight. `Shard100.lean` checks the second-largest-weight-100 shard without native axioms, in addition to the analytical exclusion through 99. It is a single new case, not the complete integer exclusion.

The ordinary search has now been checked by the Lean kernel for all second-largest weights through 101. `IntegerSearchFast` proves that the optimized search may replace the last two loops with a mask of forbidden final weights, including both moment conditions. The small `FinalTwoBenchmark` checks one terminal subcase; the optimized full evaluation for weights 102–147 is not yet verified.

`IntegerSearchWindowed` checks a conservative monotone capacity cutoff before testing a candidate's collision mask. Lean proves that this skips no valid descending completion and that a counterexample still implies a true second-weight shard. Kernel evaluation of the unverified higher shards is separate.
