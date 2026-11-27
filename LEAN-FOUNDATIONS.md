# Lean foundations under active development

The Frankl height-two cardinality bound and quadruple-avoidance fiber bound, and the poset swap injection, fixed-order bin count monotonicity, and threshold arithmetic were checked with Lean 4.36 and the repository's pinned Mathlib, using `#print axioms`. This is not a full proof of either research problem; higher-level reductions and the open cases are not included in these modules.

The workflow compiles the four modules independently of the subset sum project. The arithmetic module also builds with plain Lean.

The combined restricted theorem `FranklHeightSix.fullCoTriple_majority` also builds and has only standard axioms. It assumes the family contains all complements of at most three points, and excludes the empty set (so the statement's assumptions force ground-set size at least four). The unrestricted height-six theorem is still open here.
