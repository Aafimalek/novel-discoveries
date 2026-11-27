# Lean formalization of the 149 lower bound

These files contain checked components, **not** an end-to-end proof of 149.
Run `lake build` in this directory with the pinned toolchain.

- The finite cube neighborhood calculation and rank cut force an edge between
  ranks 158 and 306 in the separated-score model. `CriticalEdge` shows it
  changes the last coordinate when all earlier weights are smaller than 148.
- `GapBlock`, `ProjectionCount`, `ProjectionLift`, `CoordinateFraction`,
  `RoundedInterval`, and `FinsetSlab` establish subinterval spacing, projection
  bounds, the lift calculations, rank offsets along correctly rounded steps,
  and one-coordinate connectivity of finite weight slabs.
- `roundedInjective_of_center` (in `RoundedNoCollision.lean`) proves that given the central interval's
  endpoint error bounds and injectivity inside that interval, rounding is
  injective on all subsets. Its proof cancels the intersection and translates
  the disjoint pair into the interval.
- `integerMomentBoundOfDistinctSublists` derives the squared-weight lower bound
  87381 from distinct integer subset sums, with no search. At largest weight
  148, `noDistinctSublistsMax148SecondLe99` rules out all nonnegative sorted
  cases with second-largest weight at most 99.

The open formalization tasks are to instantiate and assemble the rounded
critical intervals and to exclude the remaining integer cases with largest
weight 148 and second-largest weight 100 through 147. The central geometry
lemmas are not a proof of the exact real optimum. Each cited theorem was
checked on Lean 4.36.0 and reports only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound` (or a subset of these).
