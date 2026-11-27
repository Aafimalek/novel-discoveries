# Four-point replay: maximum 148, second-largest 113

This package adds the verified **113** branch to the existing pair-packing
coverage through **112**. It does not close the full problem. The exact
remaining conditional proof obligation is second-largest **114–147**.

## Summary

* `FourPointPrinciple.lean` interprets a nonnegative, finitely supported
  integer penalty on the four signed scores (c-a-148,c-a+148,c+a-148,c+a+148).
  Distinct subset sums make the 128 blocks disjoint. A certified block
  charge `lambda` yields total score squares at least
  (128\lambda-\mathrm{budget}).
* `FourPointActual.lean` forms those blocks from the actual list
  `148 :: a :: tail`, proves parity and distinctness, and divides the
  score moment by 512. The output is a theorem about ordinary positional
  subset sums, not just about an abstract collection of disjoint blocks.
* `FourPointSymmetry.lean` reduces verification to nonnegative centers.
  Centers whose magnitude is at least 469 are cleared for both concrete
  certificates by the unpenalized quadratic block sum.
  `FourPointBudget.lean` computes the entire symmetric budget exactly as
  twice a single table sum minus its entry at zero.
* The eight anchor fragments and two budget modules check the literal
  arrays in the kernel. `FourPoint113Checked.lean` combines them,
  yielding `max148_second113_fourPoint_moment_bound`:
  the squared-weight sum must be at least **109,140**.
* `FourPoint113Shard.lean` checks the resulting finite search returns
  false and proves no actual descending tail fits the 113 branch.
* `FourPointCoverage113.lean` imports that result and the existing
  through-112 coverage. The final theorem is
  `separated_nine_at_least_149_of_remaining_shards_above_113`.
  Its one unproved argument is explicitly
  `∀ a, 114 ≤ a → a ≤ 147 → pair_packed_second_shard a = false`.

## Reproduce

The prerequisite is the already checked repository Lean project through
`NineSeparatedSubsetSums.PairPackedCoverage112` (Lean 4.36.0 and its
matching Mathlib). Copy the 18 modules listed in `verified-sources.txt`
into its `NineSeparatedSubsetSums` directory. Then build
`NineSeparatedSubsetSums.FourPointCoverage113` using the project's
standard Lake environment. Individual stages can also be checked with
`lean -j 1` in the listed order, with the usual project dependency path.
Locally, separate numeric fragments used at most about 2.85 GiB
configured Lean memory and the final import-heavy coverage used a
3.9 GiB setting. Only the final highest contiguous successful stage
is reported; failed exploratory monolithic attempts are not included.

The arrays are generated from `fourpoint113.json` by
`python make-113-split.py fourpoint113.json`. The supplied arrays and
checked proof fragments are the shipped inputs to Lean; neither Python
nor any numeric optimizer is trusted by the proof.

All closed numeric computations are `by decide +kernel`.
The full strength theorem and conditional real theorem audit only
`[propext, Classical.choice, Quot.sound]`. The closed 113 search
Boolean depends only on `[propext]`.
