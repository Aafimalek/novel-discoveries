# Real reduction calibrated to actual tail exclusions

The checked theorem `separated_nine_at_least_149_of_remaining_tails`
formalizes the final composition step. It reduces the real lower bound
to excluding actual descending seven-term tails for every integer
second-largest value from **114 through 147**, with maximum 148, and
uses the earlier already checked exclusions through 113.

The premise is expressed using `NoDescendingTail`, not a particular
search cutoff; later branches may use different four-point or
eight-point moment certificates or other legitimate exclusions.
Compile `NineSeparatedSubsetSums.CachedFourPointCoverage` in the
Lean 4.36 project containing the earlier 113 and cached-search proofs.
The theorem's only axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The theorem is conditional, not a full proof of the
real lower bound.
