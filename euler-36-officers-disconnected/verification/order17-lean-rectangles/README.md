# Lean verification of the rectangle cut

`rectangle_size_lower` shows that an unused pair in a saturated, linear order-six design with minimum degree `m` forces a candidate rectangle. If at least `r` labels remain available per side, its degree contribution is at least `r² + (6 − r)m`. `rectangleCut_holds` turns this into the archived positive three-literal clauses. Both Lean proofs use only standard axioms.

Compile this after [EulerDegreeThreshold](../order17-lean-degrees), with the project dependencies on `LEAN_PATH`. Generate the degree-one block with `lean --run EmitRectangleCut.lean > lean-rectangle.txt`; run `python3 audit_rectangles.py lean-rectangle.txt /path/to/original.cnf`. [The audit](rect-audit.log) compares all 216 rows byte-for-byte with archived degree-one branch `anchor-max-5`. This example does not supply a Lean refutation of that branch or complete the geometric coverage proof.
