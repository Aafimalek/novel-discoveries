# A finite frontier check for a specified one-NOT blocker

This is a verification shortcut, not a gate lower bound or a P vs NP
submission. The context may share gates arbitrarily.

Identify a Boolean input with the set of coordinates having value 1.
A circuit with one NOT can be written as
`F(x, not H(x))`, where the source of the NOT is the monotone function
`H`, and `F` is the monotone output context after replacing the NOT
wire by a new free input. Both functions are monotone since all their
remaining gates are monotone. Fanout does not change this argument.

Let the target be the edge function of a graph: an input is positive
exactly when it contains an edge. In either phase H=0 or H=1, the
output context restricted to the relevant last input is monotone.
Thus one needs to test only the minimal positive and maximal negative
sets in that phase: every positive extends a minimal positive, and
every negative lies below a maximal negative. The exact frontiers are:

- H=0 minimal positives: graph edges E with H(E)=0.
- H=1 maximal negatives: maximal independent sets I with H(I)=1.
- H=1 minimal positives: inclusion-minimal unions E ∪ P, with E an
  edge and P a minimal H-true set.
- H=0 maximal negatives: inclusion-maximal intersections I ∩ Q,
  with I a maximal independent set and Q a maximal H-false set.

The formulas follow because the sets containing an edge and the
H-true sets are upward closed, while the independent sets and the
H-false sets are downward closed. Their intersection frontiers are
obtained by taking minimal unions or maximal intersections as stated.

For the eight-vertex edge function in the earlier architecture
benchmark with the specific blocker H=x0, the four frontier
sizes in that order are 11, 3, 8, and 8. Thirty input vectors suffice
for any monotone context with that fixed blocker; this says nothing
about how many gates such a context needs. The companion script
independently enumerates all 256 inputs and validates the formulas.

## A dual feasibility criterion for a fixed context

Write F0=F(·,0) and F1=F(·,1), and assume F0≤f≤F1 pointwise.
The set P where f=0 and F1=1 forces H=1, while the set N where
f=1 and F0=0 forces H=0. Elsewhere the choice of H is immaterial.
A monotone blocker exists if and only if no p∈P is a subset
of n∈N. Necessity is monotonicity. Sufficiency follows by taking
H to be the indicator of the upward closure of P. This is the
least compatible blocker; the complement of the downward closure of N
is the greatest. The criterion says nothing about the circuit size
of either extremal blocker or of any intermediate one.

## Formal check

[FixedOneNot.lean](FixedOneNot.lean) verifies the separator criterion and
the fixed-context feasibility equivalence over an arbitrary reflexive,
transitive relation. These are logical lemmas, not statements about
the minimum size of a circuit. [The Lean 4.36.0 build](lean-check.log)
uses no axioms for the separator criterion and only
`propext`, `Classical.choice`, and `Quot.sound` for fixed-context
feasibility. The 30-input benchmark is independently checked by
`python3 replay.py`, not a Lean counting theorem.

Replay: `lean -j1 -M700 FixedOneNot.lean`, then `python3 replay.py`.
No external submission is claimed.
