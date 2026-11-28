# Euler all-used C03: checked geometry-to-SAT exclusion

C03 is diagram code `[111,1012,1201,1320]`. The actual Lean-generated
geometric formula for this case has no numbered satisfying valuation.
The patch checks that the geometric formula contains all 2,139 signed
clauses of the existing LRAT-refuted core and then transfers refutation
to actual geometric valuations.

The final theorems are in `LatinGap.PairEncoding.C03Linked`:

* `all_core_rows_local`: each of the 2,139 core rows belongs to the
  actual signed geometric archive formula.
* `c03_no_numbered_archive_model`: no numbered valuation satisfies
  every clause of that formula.
* `allUsed_geometry_except_c03`: every hypothetical linear, saturated,
  size-17 design with minimum label degree two, and with every pair of
  degree-two labels on distinct coordinates used, would be represented
  by some other case of the existing all-used diagram reduction.

This eliminates only C03, not the other all-used cases nor branches
with an unused pair of degree-two labels. It does not establish a
packing threshold.

## How it works

`ArchiveCoreBlocks.lean` provides case-independent row-to-archive
membership lemmas. It generalizes the previous C02 block lifts to
arbitrary case codes and adds projection-low, projection-high, and
excess-low counters. C03 uses projection-low for 32 rows. The sixteen
membership shards check each clause via exact signed row identity in
its local block. The other 2,107 rows use clause families already
exercised by C02. The proof does not reduce the complete geometric
archive, which has 60,886 clauses.

The 64-chunk formula in `C03RawFactored.lean` has the exact conjunction
tree of the checked SAT core. Its identity theorem relates the signed
rows to the actual formula refuted by `Euler.Batch.C03.coreUnsat`.
`C03Linked.lean` applies the checked numbered semantics and geometry
reduction to rule out C03. The theorem audit uses only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` and no native
computation axiom.

## Replay

Use Lean 4.36.0 and Mathlib revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Set `LEAN_PATH` to the
built Euler and Mathlib modules, including the dependencies
`EulerAllUsedFullGeometry`, `EulerAllUsedConditionalRefutations`, and
`EulerBatch.NumberedSemantics`. Use `LEAN_BIN` if needed, or run the
script in the project's `lake env`. Run `./replay.sh` for the serial
build (one worker, default interpreter cap 2500 MB). Set `REBUILD_CORE=1`
to rebuild the bundled prior core's RUP proof rather than reuse the
existing C03 core module. Run `sha256sum -c SHA256SUMS` to audit files.

Lean does not run Python. To regenerate the witness choices using
Python 3.10+, decompress `fixtures/EulerBatch/cases/03/original.cnf.gz`
to `original.cnf` in the same directory. From the package root:

```sh
CASE_DIR=fixtures/EulerBatch/cases/03 python3 plan.py
python3 verify-recipe-arithmetic.py
python3 gen-factored.py
```

The Python arithmetic replay matches every exact signed clause, but it
is only diagnostic; the Lean proof independently checks all the proposed
row identities.
