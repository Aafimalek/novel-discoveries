# Pooling two insertion ranks

Under the existing branch rank-step hypotheses, if every branch order
has the position of v at most the sum of the positions of u and w,
then the number of rankings putting a before v is at most the sum
for a before u and a before w. The proof uses antitone insertion
weights within a fixed branch order, then sums over rank triples.

There is a static sufficient condition: the count of branch vertices
not strictly above v is at most the smaller of the two anchor downset
sizes plus the size of their union. A separate corollary covers at
most five branch vertices with two distinct nonroot anchors.

Build [MultiRankStep.lean](../../lean/MultiRankStep.lean) with Lean 4.36
and the checked BranchOrder dependency. [Axiom audit](lean.log) uses
only the three standard axioms. This is a new rank inequality, not
a proof that all width-three posets have a balanced pair.
