# Size-17 Euler branch C08: complete numbered refutation

The Lean 4.36 kernel checked `Euler.Batch.C08.branchNoAssignment`
for the complete archived formula for `aus-0111_1012_1103_2220`,
an all-low-pairs-used branch (10,646 variables, 60,567 clauses).
The proof checks a pure-RUP certificate for a 5,788-clause core, then
checks the core's exact signed clause containment in the original
formula and transports the refutation. The axiom audit is
`[propext]` only. No native decision or admitted proofs were used.

The original DIMACS bytes match the published manifest, SHA-256
`494f843dc8d034ccf7d3b8041c4d1e6be4e9b099b7240e75e2ed2469752efadd`.
The archive [c08-replay.tar.gz](c08-replay.tar.gz) has SHA-256
`d53d1303bef640b19b3e0c524fcfffafc62f415841a421fe4c5935b20dcf5d29`.
Extract in a fresh working directory; with Lean 4.36 and the pinned
Mathlib on LEAN_PATH as for [previous cases](../order17-lean-batch1),
run `bash replay.sh`. The archive contains the exact numbered formula,
certificate, drivers and compile logs.

This is the ninth of 56 complete numbered size-17 refutations.
This theorem does not verify a DIMACS byte parser or the geometric
case split, and does not by itself prove the minimum arrangement size.
