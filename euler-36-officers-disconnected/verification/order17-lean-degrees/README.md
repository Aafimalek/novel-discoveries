# Lean degree threshold clauses for Euler size 17

`EulerDegreeThreshold.lean` proves that the used-pair bits in a partner coordinate count exactly the degree of any label in a linear design. It constructs the archived unary threshold clauses over literal IDs 9719–9886, verifies the IDs are distinct, and proves every clause holds for the intended degree valuation subject to the branch's minimum and anchor degree. The axiom audit uses only the standard Lean axioms.

With the existing `EulerNumbering` module and its dependencies compiled and on `LEAN_PATH`, compile `EulerDegreeThreshold.lean`, then use `lean --run EmitDegreeBlock.lean > lean-block.txt`. Run `python3 audit_degrees.py lean-block.txt C01=/path/to/case01.cnf ...`. This compares all 6,888 clause rows emitted by the Lean generator against each corresponding original byte slice. Five tested originals are in the [kernel replay package](../order17-lean-batch1); C05 is a separately regenerated case and has not been kernel-refuted by that batch.

The geometric minimum and anchor assumptions, other branch clauses, and the DIMACS byte parsing link do not follow from this module alone. No claim of an end-to-end Lean lower bound is made.
