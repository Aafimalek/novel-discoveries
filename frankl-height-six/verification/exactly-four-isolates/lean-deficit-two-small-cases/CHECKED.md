# Checked deficit-at-most-two incidence and small-source branches

For a pair design with all source degrees at least k−3, the local
endpoint checks that each block has size at most four, every point
has triple degree plus twice quad degree at most two, and each quad
is disjoint from every other nonpair block. The global budgets
check (N+2t+5u=\binom{k}{2}), (3t+8u\le2k), and
(3(2t+5u)\le4k).

Actual-family endpoints for exactly four isolated points:
- `FranklForcingFiber.exact_four_deficit_le_two_not_sole_quad`
  excludes a sole nonpair quad for any number of sources.
- `FranklForcingFiber.exact_four_deficit_le_two_not_small_sources`
  excludes two to four sources under the stated source-degree bound.

Larger-source deficit-two cases and proof of an upstream deficit bound
are not covered. The replay uses pinned ordinary Lean 4.36, Mathlib,
one worker, 2500 MB, warning as error, and overlay temporary storage.
