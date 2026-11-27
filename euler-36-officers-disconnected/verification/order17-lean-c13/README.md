# Size-17 Euler branch C13: complete numbered refutation

The Lean 4.36 kernel checked `Euler.Batch.C13.branchNoAssignment`
for all 60,248 clauses of the archived formula for
`aus-0111_1012_2203_2320` (10,646 variables).
The 6,937-clause pure-RUP core and its exact signed containment in the
original formula were both checked. Only `propext` is used.

The original DIMACS SHA-256 is
`e458f9cdee1f887d9b4c9fff88b67651052b326c289b73f3344bc962e8605b2a`.
The [replay archive](c13-replay.tar.gz) has SHA-256
`0464130e23d763be6021026f5ca9c855637e02f92571fc9d60706c13c297928e`.
Unpack it and run `bash replay.sh` with Lean 4.36.0 and the pinned Mathlib.
The core is substantially larger than the initial pilot.

This brings the complete numbered size-17 refutations to 12 of 56.
The geometry-to-all-formulas implication and other refutations remain.
