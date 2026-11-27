# Lean bridge for the numbered size-17 core

The checked Lean theorems here formalize the numeric word/pair ID
allocation, the interpretation of signed DIMACS literals, and the
support AMO auxiliary counter used by PySAT.

- `EulerNumbering.lean` proves `varNumber_injective`,
  `numberedHolds_iff`, and `numberedCandidate_iff`. All printed
  axiom audits contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `EulerSequentialAMO.lean` proves `sequentialAMO_iff`: an
  at-most-one sequence of chosen-word bits is equivalent to existence
  of a satisfying assignment to the sequential state bits. The
  axiom audit contains only `propext` and `Quot.sound`.

Compile `EulerNumbering.lean` after the published `EulerPairClauses`
file and `EulerSequentialAMO.lean` after `EulerNumbering.lean`.

`audit_prefix.py /path/to/original.cnf` separately compares the
construction numerically to the exact archived DIMACS bytes for
`aus-0111_1012_1203_1320`. It checks the SHA-256, then reproduces
all 31,752 clauses of the original prefix, including every
sequential-counter clause. The physical variable ranges are:

| Meaning | One-based DIMACS IDs |
|---|---|
| Chosen words | 1–1296 |
| Used pairs | 1297–1512 |
| Support AMO states | 1513–9072 |

The comparison script is not a Lean parser proof. The remaining
28,815 trailing clauses include exact cardinality, degrees,
additional cuts, and case-specific constraints. This bridge does
not yet prove that a geometric design sets all clauses of the exact
CNF, does not check any DRAT/LRAT certificates, and does not itself
prove the lower bound 18.
