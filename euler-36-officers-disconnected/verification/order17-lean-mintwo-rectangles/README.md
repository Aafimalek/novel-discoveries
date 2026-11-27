# Exact minimum-two Euler candidate rectangle propagation

For a linear saturated order-six design, consider an unused pair of
degree-at-most-two labels. If the opposite group contains a common used
neighbor, there are at least three labels in that group unused with
both endpoints: the union of the two neighbor sets has size at most
three. Each label on the other side unused with both endpoints must be
used with every one of those three candidates, by saturation. Its
frequency is therefore at least three.

`EulerMinTwoCandidateRectangle` proves this geometric implication and
the exact numbered clause family. The two degree loops in original
`min2_f17_pinned.py` generate no unguarded clause and generate guarded
clauses only at (dx,dy)=(2,2). Thus the modeled block consists of 15,552
eight-literal clauses in the exact order. The theorem holds for any
numbered valuation with actual pair and degree bits, without a design
size or global minimum assumption.

`EulerMinTwoCandidateAssembly` adds that block to the same valuation
already checked for the 34,594 modeled common and pin/profile clauses
on an actual size-17 all-used design. It does not install new bits.
This totals 50,146 physical modeled clauses per selected diagram, not
whole formula satisfiability or unsatisfiability. Base degree tables,
base degree sorting, repeated saturation lines, and final free-label
lex symmetry are not asserted by this assembly.

Compile the two files in the above order using Lean 4.36.0 and matching
Mathlib, with the checked overlap-orientation and all-used pin/geometry
dependencies on the Lean path. To replay the independent original-byte
audit, run `lean --run EmitMinTwoRectangle.lean > emitted-candidate.txt`
and `python compare_candidate_rectangle.py emitted-candidate.txt
PATH_TO_ALL_LOW_PAIRS_USED_ARCHIVE` using `python-sat==1.8.dev24`.
The audit compares whole signed clause arrays in exact order with
hash-verified originals; it is not a theorem about a formal parser.
