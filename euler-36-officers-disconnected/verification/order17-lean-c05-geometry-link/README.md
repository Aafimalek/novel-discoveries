# Euler all-used C05: checked geometry-to-SAT exclusion

The exact diagram code is `[111,1012,2201,3120]`. Lean checks all 5,036
signed clauses of the already LRAT-refuted core in the actual geometric
archive of 60,567 clauses, then transfers refutation to numbered
valuations. The exact matched prior checker is `EulerBatch.C05CoreSorted`
with theorem `Euler.Batch.C05.coreUnsat`.

The final theorem `LatinGap.PairEncoding.C05Linked.allUsed_geometry_except_c05`
rules out this one case for hypothetical linear, saturated, size-17
designs with minimum degree at least two and every pair of degree-two
labels on distinct coordinates used. It does not address the other
cases or prove a packing threshold.

The checked main theorem and independent import audit use only
`propext`, `Classical.choice`, and `Quot.sound`. There is no
`sorryAx` or native evaluation axiom. Source logs and exact historical
checker inputs are included. The recorded verification used two bounded
sessions: the first stopped after shard 15, and the second checked the
saved source, receipts, and object hashes. It imported all 64 first-half
chunk proofs before compiling shards 16–31, linking, and auditing. The
checkpoint object hashes record local binaries; those binaries are not
bundled. The full source replay below compiles them all.

## Reproduce

Use pinned Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Put the built Euler
geometry, numbered semantics, and matching prior core modules on
`LEAN_PATH`. Run `./replay.sh . C05` for a serial build and fresh
audit, one worker, interpreter cap 2500 MB by default.

If the prior core object is unavailable, build its bundled
`fixtures/EulerBatch/C05CoreSorted.lean` from the fixtures
root after building its bundled `EulerBatch.FactoredDriver` and adding
that module directory to `LEAN_PATH`. The matching exact CNF and LRAT
inputs are included.

Kernel checking does not use Python. The diagnostic witness chooser
and generator can be replayed with:

```sh
./prepare_case.sh \
  --original fixtures/EulerBatch/cases/05/original.cnf.gz \
  --core fixtures/alternatives/05/1.cnf --codes 111,1012,2201,3120 --bridge C05 \
  --core-module EulerBatch.C05CoreSorted --core-theorem Euler.Batch.C05.coreUnsat \
  --out ./c05-reproduction
```

Check staged bytes with `sha256sum -c SHA256SUMS`.
