# Aggregate checked tail range through 119

`ClosedTailRange119.lean` proves `noDescendingTailsThrough119`:
for every integer 114 ≤ a ≤ 119, the maximum-148,
second-largest-a branch has no descending integer tail.
This aggregates six separately checked mathematical exclusions.

`CachedFourPointCoverage.lean` proves the conditional real theorem
`separated_nine_at_least_149_of_remaining_tails`. It uses the
earlier checked branches through 113 and takes the actual tail
exclusion proposition for each remaining value. These modules
do not claim an unconditional real lower bound, or any new
complete second-largest branch above 119.

Compile with Lean 4.36 in the project's existing module environment,
including the checked 113, cached search, and 114–119 checkpoints.
Both included theorems use only `propext`, `Classical.choice`,
and `Quot.sound`.
