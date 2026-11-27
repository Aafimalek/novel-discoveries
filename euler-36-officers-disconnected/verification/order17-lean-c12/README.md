# Size-17 Euler branch C12: complete numbered refutation

The Lean 4.36 kernel checked `Euler.Batch.C12.branchNoAssignment`
for all 60,248 clauses of the archived formula for
`aus-0111_1012_1203_2320` (10,646 variables).
The 7,089-clause pure-RUP core and its exact signed containment in the
original formula were both checked. Only `propext` is used.

The original DIMACS SHA-256 is
`b3370d65e6f916fa59b75a83109010c3285f63bc72a4169d9d4940e2f705871e`.
The [replay archive](c12-replay.tar.gz) has SHA-256
`7b8066498e89110be78baaeddfea13693577bf69c5d8efee15fef20abf730c46`.
Unpack it and run `bash replay.sh` with Lean 4.36.0 and the pinned Mathlib
on LEAN_PATH, as for [the previous batch](../order17-lean-batch1).

This brings the complete numbered size-17 refutations to 11 of 56.
The geometry-to-all-formulas implication and other refutations remain.
