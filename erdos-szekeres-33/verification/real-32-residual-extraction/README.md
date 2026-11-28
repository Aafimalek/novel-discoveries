# Actual real 33-point residual extraction

Pinned Lean 4.36.0 checks that a real 33-point counterexample to the convex
heptagon statement yields an ordered, actual real 32-point embedding satisfying
the residual constraints. It can be chosen to satisfy the symmetry-breaking
lexicographic order for any supplied reflection pair list.

The separate orbit module checks that ordered triple reversal has no fixed
point, interchanges the selected side, and gives exactly one representative
per ordered orbit in its enumerated list. The 2,480 count is an independent
finite Python audit, not a numerical Lean theorem.

The extraction and conditional composition use only
`propext`, `Classical.choice`, and `Quot.sound`.
There is no result about the literal DIMACS formula or target UNSAT here.
The 33-point theorem remains open.

The archive includes the complete 17-module local source closure, explicit
build order, stage receipts, orbit audit and replay instructions. Individual
modules were checked in their exact dependency stack; a second fully fresh
17-module replay was not run when assembling this release.
