# Exact archived all-used free-label lex suffix

This extension uses the exact preceding non-lex archive model. It
generates precisely the remaining suffix corresponding to the Python
`tie` function: each adjacent pair of free labels, each possible first
difference, each common Boolean prefix in product order, and each
degree threshold in 2–6. There are 315 clauses per adjacent pair.
The group 0 partner is group 1 and every other group uses partner 0,
matching the earlier numbered degree encoding.

`archiveAllUsedLex_holds` proves all suffix clauses for a valuation
whose incidence rows satisfy `ArchivedIncidenceLE` on each specified
adjacent pair. It is a conditional theorem: it does not establish
existence of that simultaneous relabeling on actual geometry. It
does not claim an end-to-end geometry reduction or any SAT refutation.

Compile `EulerAllUsedLex.lean` using Lean 4.36.0 and matching Mathlib,
with `EulerAllUsedNonLex` and its verified import closure on
`LEAN_PATH`. See the axiom audit in `lex.log`. To compare against
the archived DIMACS originals independently, run
`lean --run EmitAllUsedLex.lean > emitted-lex.txt`, then
`python compare_lex.py emitted-lex.txt PATH_TO_ALL_USED_ARCHIVE`
using `python-sat==1.8.dev24`. The audit matches every signed row in
order and independently verifies the original DIMACS hashes, but is
not a checked parser theorem.

[Replay archive](euler-allused-conditional-lex-replay.tar.gz) · SHA-256 `dc2ab169c1a74dc63022297b71ad82eb97c7be2ea75f34c1d2f74fe0a9f411bd`.
