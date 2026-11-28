# Euler all-used C07: checked geometry-to-SAT exclusion

The exact diagram code is `[111,1012,1201,2320]`. Lean checks all 3,501
signed clauses of the already LRAT-refuted core in the actual geometric
archive of 60,567 clauses, then transfers refutation to numbered
valuations. The exact matched prior checker is `EulerBatch.C07Core`
with theorem `Euler.Batch.C07.coreUnsat`.

The final theorem `LatinGap.PairEncoding.C07Linked.allUsed_geometry_except_c07`
rules out this one case for hypothetical linear, saturated, size-17
designs with minimum degree at least two and every pair of degree-two
labels on distinct coordinates used. It does not address the other
cases or prove a packing threshold.

The checked main theorem and independent import audit use only
`propext`, `Classical.choice`, and `Quot.sound`. There is no
`sorryAx` or native evaluation axiom. Source logs and exact historical
checker inputs are included.

## Reproduce

Use pinned Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Put the built Euler
geometry, numbered semantics, and matching prior core modules on
`LEAN_PATH`. Run `./replay.sh . C07` for a serial build and fresh
audit, one worker, interpreter cap 2500 MB by default.

If the prior core object is unavailable, build its bundled
`fixtures/EulerBatch/C07Core.lean` from the fixtures
root after building its bundled `EulerBatch.FactoredDriver` and adding
that module directory to `LEAN_PATH`. The matching exact CNF and LRAT
inputs are included.

Kernel checking does not use Python. The diagnostic witness chooser
and generator can be replayed with:

```sh
./prepare_case.sh \
  --original fixtures/EulerBatch/cases/07/original.cnf.gz \
  --core fixtures/EulerBatch/cases/07/core.cnf --codes 111,1012,1201,2320 --bridge C07 \
  --core-module EulerBatch.C07Core --core-theorem Euler.Batch.C07.coreUnsat \
  --out ./c07-reproduction
```

Check staged bytes with `sha256sum -c SHA256SUMS`.
