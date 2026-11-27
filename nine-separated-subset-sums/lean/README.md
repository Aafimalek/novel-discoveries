# Lean verification of the real-to-integer reduction

The full real argument is checked in [`RealReduction.lean`](NineSeparatedSubsetSums/RealReduction.lean). The theorem `real_counterexample_reduces_to_integer` proves that nine positive real weights with pairwise unit-separated subset sums and largest weight below 149 yield nine positive integer weights, largest weight exactly 148, whose subset sums are all distinct.

The proof sorts the real scores, uses the nine-dimensional cube cut to force the first critical block, checks the rounding along its projected coordinate paths, then uses reflection and translates every hypothetical collision into the central block. The corollary `separated_nine_at_least_149_of_integer_exclusion` proves the lower bound **conditional on the explicit finite integer exclusion in its statement**. Both theorems compile with Lean 4.36.0 and report only `propext`, `Classical.choice`, and `Quot.sound`.

**The remaining Lean task is the integer exclusion.** The ordinary search excludes every second-largest integer weight through 101, and the capacity-windowed search excludes 102 and 103. The two windowed evaluations depend only on `propext`. [`IntegerShardCoverage.lean`](NineSeparatedSubsetSums/IntegerShardCoverage.lean) proves that any genuine max-148 counterexample would pass both searches at the same second-largest weight, and combines the disjoint checks to leave only **104–147**. That combined theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

The [independent C++ exhaustive search](../verification/integer-search.md) found no candidate at exact maximum 148, but a C++ run is not a Lean certificate for the unchecked cases. The lower bound is not yet verified end to end in Lean, and the exact real optimum remains in [149, 161].

`IntegerSearchInput` proves that a counterexample makes the search return true. `IntegerSearchFast` verifies the terminal two-weight collision mask, including the moment checks. `IntegerSearchWindowed` verifies that a monotone capacity cutoff before each recursive mask test skips no valid completion. Correctness of a search and kernel evaluation of its output are separate.

From this directory, run `lake build` with the pinned toolchain. Each module prints its axiom audit. See the [written paper](../paper/nine-separated-subset-sums.pdf) for the lower bound.
