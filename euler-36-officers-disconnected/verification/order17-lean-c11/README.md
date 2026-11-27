# Size-17 Euler branch C11: complete numbered refutation

The Lean 4.36 kernel checked `Euler.Batch.C11.branchNoAssignment`
for the complete archived formula for `aus-0111_1012_2201_1320`,
an all-low-pairs-used branch (10,646 variables, 60,567 clauses).
The proof first checks a pure-RUP certificate for a 5,250-clause core;
the kernel then checks that the exact signed core clauses occur in the
original formula and transports the refutation. The axiom audit is
`[propext]` only. No native decision or admitted proofs were used.

The bytes of the original DIMACS file have SHA-256
`f57a9ca269089e18a8fd587fe0a76be0e3aa858f361680acc153662dd0d49a0d`.
The archive [c11-replay.tar.gz](c11-replay.tar.gz) has SHA-256
`c753b9ef0840dc1f14291f2ea54665f5e6f2f27a2e732b6897f1f3a5985ae791`.
Extract in a fresh working directory; with Lean 4.36 and the pinned
Mathlib on LEAN_PATH as for [the previous cases](../order17-lean-batch1),
run `bash replay.sh`. The archive contains the exact numbered formula,
certificate, drivers and compile logs.

This is the eighth of 56 complete numbered size-17 refutations.
This theorem does not verify a DIMACS byte parser or the geometric
case split, and does not by itself prove the minimum arrangement size.
