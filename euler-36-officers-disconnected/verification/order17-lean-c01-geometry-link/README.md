# Euler all-used C01: checked geometry-to-SAT exclusion

The exact diagram code is `[111,1012,1103,1220]`. Lean checks all 2,215
signed clauses of the already LRAT-refuted core in the actual geometric
archive of 60,886 clauses, then transfers refutation to numbered
valuations. The exact matched prior checker is `EulerBatch.C01Core`
with theorem `Euler.Batch.C01.coreUnsat`.

The final theorem `LatinGap.PairEncoding.C01Linked.allUsed_geometry_except_c01`
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
`LEAN_PATH`. Run `./replay.sh . C01` for a serial build and fresh
audit, one worker, interpreter cap 2500 MB by default.

If the prior core object is unavailable, build its bundled
`fixtures/EulerBatch/C01Core.lean` from the fixtures
root after building its bundled `EulerBatch.FactoredDriver` and adding
that module directory to `LEAN_PATH`. The matching exact CNF and LRAT
inputs are included.

Kernel checking does not use Python. The diagnostic witness chooser
and generator can be replayed with:

```sh
./prepare_case.sh \
  --original fixtures/EulerBatch/cases/01/original.cnf.gz \
  --core fixtures/EulerBatch/cases/01/core.cnf --codes 111,1012,1103,1220 --bridge C01 \
  --core-module EulerBatch.C01Core --core-theorem Euler.Batch.C01.coreUnsat \
  --out ./c01-reproduction
```

Check staged bytes with `sha256sum -c SHA256SUMS`.
