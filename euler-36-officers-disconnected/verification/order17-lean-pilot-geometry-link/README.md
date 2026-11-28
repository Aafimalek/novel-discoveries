# Euler all-used Pilot: checked geometry-to-SAT exclusion

This patch connects diagram code `[111,1012,1203,1320]` to the
prior 2,646-clause pilot RUP refutation. It is called Pilot to distinguish
it from EulerBatch C10, which is a different degree-one case.

Lean verifies the 2,646 actual local clause memberships in the
geometrically generated all-used archive (60,567 clauses total). It
checks their exact signed syntax against the already refuted formula
of the prior module `FactoredCore` (with the
global theorem name `allused_core_unsat_factored`) and passes
numbered satisfaction through the existing semantics bridge.

Final declarations in `LatinGap.PairEncoding.PilotLinked`:

- `all_core_rows_local`: every one of the 2,646 signed core rows
  belongs to the actual geometric formula.
- `pilot_no_numbered_archive_model`: the actual geometric formula has
  no satisfying numbered valuation.
- `allUsed_geometry_except_pilot`: a hypothetical linear, saturated,
  size-17 design of minimum degree two, with every pair of degree-two
  labels on distinct coordinates used, must be represented by a
  different published all-used case.

The independent import audit uses only `propext`, `Classical.choice`,
and `Quot.sound`; there is no `sorryAx` or native computation axiom.
This excludes only this one branch, not the other branches or the
whole packing threshold.

## Replay

Use pinned Lean 4.36.0 / Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Configure `LEAN_PATH`
with the compiled Euler geometry and numbered semantics dependencies
plus the matching Lean-checked `FactoredCore` module. Run
`./replay.sh . Pilot`. The driver uses one worker, default 2500 MB
interpreter cap, and concludes with an independent import audit.

If needed, build the bundled previous checker from
`fixtures/Pilot/FactoredCore.lean`, with that directory as the
source root so its relative CNF and LRAT files resolve, and put the
result on `LEAN_PATH`. The old checker source and certificate are
unchanged.

The mathematical proof does not call Python. To regenerate the
untrusted local row witnesses and the emitted proof sources:

```sh
./prepare_case.sh \
  --original fixtures/Pilot/original.cnf.gz --core fixtures/Pilot/core.cnf \
  --codes 111,1012,1203,1320 --bridge Pilot \
  --core-module FactoredCore --core-theorem allused_core_unsat_factored \
  --out ./pilot-reproduction
```

The original exact row witness diagnostics are in `logs/`. Verify
staged files with `sha256sum -c SHA256SUMS`.
