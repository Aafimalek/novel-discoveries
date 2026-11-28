# Lean verification of the classical upper bound 161

The exact theorem `NineSeparatedSubsetSums.separated_nine_upper_161` gives
positive weights `w : Fin 9 → ℝ`, all at most 161 with a weight equal to
161, whose distinct finite subsets have sum differences of absolute
value at least 1. This checks the upper endpoint only and does not
determine the optimum or prove the independent lower bound.

The witness is 77, 117, 137, 148, 154, 157, 159, 160, 161, the
nine-element Conway–Guy set in [Borwein and Mossinghoff, Table 5](https://www.cecm.sfu.ca/~pborwein/PAPERS/P170.pdf).
There is no dependence on the claimed minimality of the integer witness.

The natural certificate enumerates all 512 sublists of `List.finRange 9`.
For any finite subset, filtering `List.finRange 9` by its membership gives
an enumerated representative with exactly the specified finite sum.
The checker examines the list of scores using a natural-number bitmask
that records each score; its formal invariant identifies set bits with
precisely the scores already processed. Lean's kernel reduces the check
via `decide +kernel`. The real module proves the natural-to-real sum
cast and uses strict natural inequalities to establish separation.
There are no supplemental project imports, native decisions, or
unproved assumptions. The axiom audit reports exactly
`[propext, Classical.choice, Quot.sound]`.

Use Lean 4.36.0 and Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. With the usual Mathlib
`LEAN_PATH` inherited (e.g. via `lake env` from a Mathlib project), run
`./replay.sh` from this packet. It uses one Lean process at a time,
builds both source modules and checks a fresh import of the exact
statement. The included `replay.log` records the three successful
runs; observed peak RSS was under 924 MiB. For a faster machine or
different library version resource limits may be overridden by setting
`LEAN_MEMORY_MB` (default 960, Lean's own allocator cap).
