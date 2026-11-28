# Lean reduction: an ES33 counterexample satisfies the internal endpoint CNF

This source closure reproduces the **conditional** Lean reduction for the
unaugmented, positive-anchor target: 32 residual labels, no 7-cap, no
6-cup, no common-endpoint opposite chains forming a 7-gon.

The checked endpoint in `src/RealChainExclusions.lean` is
`ES33.EndpointConcrete.es33_of_internal_target32_unsat`: if the exact
Lean-compiled numbered formula is unsatisfiable, every general-position
33-point plane embedding has a seven-point subset in convex position.
There are no auxiliary propagation, exclusion, clause-exhaustiveness,
or dictionary-support hypotheses in this theorem. The only problem-
specific premise is UNSAT of that internal formula.

The complete forward route is: a real counterexample yields an actual
32-point projective-chart real witness; its orientations and exact
chain-existence valuation satisfy guarded propagation and exclusions;
every typed clause is covered by the actual dictionary and satisfied;
the checked compiler transports that valuation to the numbered formula.
For the geometric cross exclusion, the positive and negative chains
with common endpoints produce an even set by the selected median
sign rule and have exactly the two endpoints in common.

**This does not prove UNSAT or ES(7)=33.** Nor does it identify the
external DIMACS parser's loaded clause object, or include the distinct
reflection-lex augmentation. `pilot/` gives a smallest bounded bridge
proposal and a six-row source fixture; its theorem has not been run.

## Source and historical receipts

`src/` contains exactly the 33 local Lean modules transitively imported
by `RealChainExclusions`. `build-order.txt` is topological; all local
namespaces and file paths are kept intact, including every `ES33.*`
module. Lean 4.36.0 (x86-64 Linux executable SHA-256
`db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00`)
and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
are the checked toolchain; the Mathlib dependency manifest is included.

The source bytes have 28 matching source-hash/exit-zero historical
receipts plus five pinned historical sources with their prior audit
logs. The endpoint's three theorem axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.
The individual historical checks used the then-verified dependency
stack. **No new all-33 clean build is claimed.** Header comments
referring to drafts are preserved where needed to retain the exact
historically checked source bytes.

Run the static preflight without invoking Lean:

    python3 replay.py

A future explicitly approved fresh replay uses one namespaced output
root, one pinned Lean worker, warnings as errors, overlay TMPDIR,
2250 MB Lean and 2310000 KiB sampled RSS limits, 150 s per module,
and hash and axiom logs. Supply the exact Mathlib build library roots
(including its pinned dependency packages):

    python3 replay.py --compile-approved \
      --lean /absolute/path/to/lean \
      --out /absolute/path/to/new-overlay \
      --mathlib-lean-path /mathlib/build/lib/lean:/package/build/lib/lean

A full replay may take several minutes and has not been executed here.
The exploratory six-row Python fixture check is independent of both
the historical Lean receipts and the future Lean linkage.
