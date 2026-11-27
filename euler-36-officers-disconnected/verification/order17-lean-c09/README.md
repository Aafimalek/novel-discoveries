# Size-17 Euler branch C09: complete numbered refutation

The Lean 4.36 kernel checked `Euler.Batch.C09.branchNoAssignment`
for all 60,567 clauses of the archived formula for
`aus-0111_1012_1203_2120` (10,646 variables).
The 5,649-clause pure-RUP core and its exact signed containment in the
original formula were both checked. Only `propext` is used.

The original DIMACS hash matches the published manifest:
`67e09b89cb0021fd78866af2b53c2597ae0944c4339d63062da38097d4bf0b42`.
The [replay archive](c09-replay.tar.gz) has SHA-256
`5e91ffc37713e154e88e37d5f18daa8b5a4eb7bfbd6baa5ab7224baf26ccf0f5`.
Unpack it and run `bash replay.sh` with Lean 4.36.0 and the pinned Mathlib
on LEAN_PATH, as for [the previous batch](../order17-lean-batch1).

This brings the complete numbered size-17 refutations to 10 of 56.
The geometry-to-all-formulas implication and other refutations remain.
