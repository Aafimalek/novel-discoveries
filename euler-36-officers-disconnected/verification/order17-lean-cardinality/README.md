# Exact-cardinality blocks for the order-six archived branch

`EulerSequentialCount.lean` verifies the truncated rectangular
sequential counter: it has satisfying auxiliary bits iff the count
of selected inputs satisfies the stated upper bound. Its witness is
the prefix-threshold valuation. Two separate counters, one on the
complemented input, give exact cardinality. In addition to the
generic theorems, Lean checks the exact-17-of-36 projection block
and the exact-5-of-24 block used once per group for degree excess.
The printed axiom audits use only `propext`, `Classical.choice`,
and `Quot.sound`.

`audit_cardinality.py /path/to/original.cnf` independently expands
the Lean-described clause families in the original PySAT order
and checks their signed literals one by one against the original
archived DIMACS. It confirms:

- Clauses **31,753–33,044**: exact 17 among pair bits **1297–1332**
  representing the first projection. Sequential-counter auxiliary
  IDs **9073–9718**.
- Clauses **41,263–42,782**: four exact-5 degree-excess counters.
  Each sees the four threshold bits for degrees 3 through 6 for
  each of the six labels in one coordinate. Sequential-counter
  auxiliary IDs **9887–10646**.

These are 2,812 additional audited clauses beyond the independent
31,752-clause core prefix. Match-to-DIMACS is a byte audit, not part
of the Lean checker. Unary thresholds, later branch-specific
clauses and symmetry cuts are not covered by this bridge, nor
does it prove the branch's UNSAT certificate. To compile the module,
first build `EulerSequentialAMO` from the existing normalized
numbering bridge.
