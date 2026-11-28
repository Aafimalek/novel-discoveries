# Euler 36 officers, size-17 saturated partial packing: exclusion of all-used case C02

This patch supplies the checked link between the geometric encoding and
one refuted SAT branch. In `LatinGap.PairEncoding.C02Blocks`, the geometry's
C02 code is `[111,1012,1201,1120]`. The theorems are:

* `all_core_rows_local`: all 968 signed clauses of the refuted core occur
  in the actual Lean-defined `archiveAllUsedCNF codes`.
* `c02_no_numbered_archive_model`: there is no numbered valuation satisfying
  every clause of that actual geometric formula.
* `allUsed_geometry_except_c02`: if a linear, saturated size-17 design on
  four six-symbol coordinates has degree at least two everywhere and every
  pair of degree-two labels on different coordinates is used, then it is
  represented by a satisfying numbered model of **some other** case in the
  existing published-diagram reduction.

The last theorem excludes only this one branch. It does not rule out all
such size-17 designs, address the branches where a degree-two pair is
unused, or establish a packing threshold.

## How the proof is checked

The eight membership modules check individual exact signed-integer
clause identities inside the appropriate geometric blocks, then lift
membership through the actual archive generator. The proof never
normalizes the entire 61,205-clause formula. `C02RawFactored.lean` checks
the signed-list-to-SAT conversion and the identity to the existing
LRAT-refuted formula; its 32 chunks use the same conjunction tree as
Mathlib's SAT builder. The prior refutation `Euler.Batch.C02.coreUnsat`
checks on the bundled local fixture. `C02Linked.lean` connects this with
actual geometric valuations through the checked numbered semantics,
and calls the established geometry reduction. The theorem audit lists
only `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorryAx` or native computation axiom.

## Replay

This is a source patch for the existing Euler Lean project; it is not a
standalone replacement for its geometric development. Use Lean 4.36.0 and
Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Build the
existing Euler dependencies first, including
`EulerAllUsedFullGeometry`, `EulerAllUsedConditionalRefutations`, and
`EulerBatch.NumberedSemantics`. The checksums of the two direct geometric
prerequisites are in `logs/geometric-prerequisite-sources.sha256`.

Set `LEAN_BIN` to the Lean executable and `LEAN_PATH` to the built Euler
and Mathlib module directories (for a single Lake build, run the script
under that project's `lake env`). Run `./replay.sh`. It runs one worker
with a default interpreter memory setting of 2500 MB. If the C02 refutation
has not yet been built or a replay of it is wanted, set
`REBUILD_C02_CORE=1` to compile its included factored RUP driver and replay
the bundled CNF/LRAT before checking the new sources. All recorded
successful checks are under `logs/`; verify the files with
`sha256sum -c SHA256SUMS`.

Proof checking does not call Python. To regenerate the witness choices
from the archive, decompress `fixtures/EulerBatch/cases/02/original.cnf.gz`
to `original.cnf` in the same directory. Run
`C02_CASE_DIR=fixtures/EulerBatch/cases/02 python3 plan.py`, then
`python3 gen-factored.py`. The supplied row-to-block witness choices
are untrusted inputs to the kernel-checked membership identities.

Complete source, fixtures and receipts: [replay archive](euler-c02-geometry-replay.tar.gz), SHA-256 `6345449da4146d07151c775b249a291396e8697dc8886b527b97e120e55d0798`. Extract it before running the internal checksum and replay commands above.
