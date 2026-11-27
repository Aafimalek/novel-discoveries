# Verified 2 by 3 branch theorem

Main theorem: `WidthThree.balanced_of_twoByThreeShape` in `lean/Integrated23Check.lean`.

For a finite poset with the usual good-pair predecessor inclusion, suppose the exclusive upset of b consists exactly of b and the ordered arms x < X and y < Y < Z above it. A balanced pair exists if the count for a < b is at most 7/30 of the total. The sufficient threshold is 1/4 if x < Z in the poset. Other cross-arm comparisons are allowed. The result is local to this branch shape and does not settle the general width-three conjecture.

The proof classifies actual rankings as a branch order and insertion cut, applies order-fibre bin monotonicity, decomposes the antitone histograms into nonnegative cutoff weights, derives the strict majority order under no balance, and rules out that order by the checked finite table. The separate obstruction verifies a 15/62 antitone mixture with no balance. It is not a poset counterexample. The checked example shows that a quarter guarantee fails in the cutoff model without the additional comparison.

## Build order

The new Lean modules, in dependency order, are:

1. `TwoByThreeReplay` (exact certificate table)
2. `TwoByThreeWeights` and `MajorityOrderClassify`
3. `TwoByThreeMajority`
4. `Integrated23Check` (uses the existing project module `BranchOrder`)
5. `TwoByThreeObstruction` (depends only on `TwoByThreeReplay`)

Validation used plain Lean 4.36.0 and pinned Mathlib, with the existing BranchOrder proof and a minimal-import build of its BranchSwap dependency. The source audit is in `logs/`: standard axioms only. No external solver is used by Lean. The original certificate generator and inputs are in `generator/`; `gen.py` recreates the replay module and `gen-mix.py` recreates the numeric mixture proof included in the integrated file.

## Existing modules and avoiding duplicates

The exact prerequisite sources used for the local audit are preserved under
`prerequisite-reference/`. The Lean build directory should contain only one
copy of each existing `BranchSwap` and `BranchOrder` module; these reference
copies are not new build targets. `BranchOrder.lean` is unchanged from the
already checked branch-order proof. `BranchSwap.lean` has the same declarations
and proofs, with narrower Mathlib imports for the audit.

The integrated proof includes the full ranking-histogram and weighted-mixture
declarations. Do **not** add or import the earlier standalone
`TwoByThreeMixtures`, `TwoByThreeClassify`, or `TwoByThreeRankingBridge` into
the same Lean build when using this integrated target. The replay and
obstruction modules are identical to the earlier numeric stage, so keep one
copy of each. The original two-by-two result and the independent rank-pooling
lemma do not duplicate these declarations.
