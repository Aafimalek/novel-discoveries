# Exact Euler all-used pin/profile and common valuation

These checked Lean files connect the normalized actual four outer
placements to the archived size-17 all-used formulas.

- `EulerAllUsedPinProfile` proves that the decimal rendering and decoder
  agree for every order-six word. It models the original two base
  anchor units, the four archived branch-specific word pins, and the
  24 exact signed units on threshold-three bits.
- Zero labels in two distinct groups occur together in 0000. The six
  derived positive pair bits are proved as semantic consequences; they
  are not claimed to be additional physical singleton clauses.
- `EulerAllUsedPinCommon` installs a single valuation satisfying these
  clauses and the independently checked common support and cardinality
  blocks. It assumes the normalized exact degree profile and actual
  membership of the four published words.

Build both modules in this order with Lean 4.36.0 and matching Mathlib;
place the checked actual-diagram, common prefix/counters, and degree
modules on the Lean path. The included Lean logs give the axiom audit.
The independent emission audit, when included, compares signed integers
in exact order with hash-verified originals; it is not a Lean parser
proof. Neither these checked proofs nor the independent audit certify
free-label symmetry, all remaining clause families, or whole-formula
unsatisfiability.

The extended build proves the initial degree profile geometrically,
threads it through every coordinate and column relabeling, and connects
the result to the same checked valuation. Compile
`EulerAllUsedProfilePreserved` and `EulerAllUsedGeometryPinLink` after
the two initial modules. The final theorem `allUsed_geometry_pin_link`
assumes only a linear saturated design of size 17, minimum label degree
two, and use of every low-low pair across distinct groups. It yields
one of the published diagrams with a valuation satisfying the 34,594
modeled physical clauses plus the six separate derived bits.
