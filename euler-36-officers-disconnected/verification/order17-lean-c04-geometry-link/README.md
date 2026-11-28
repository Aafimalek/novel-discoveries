# Euler all-used C04: checked geometry-to-SAT exclusion

C04 is diagram code `[111,1012,1201,2120]`. The full original branch
formula has 60,886 rows. Its archived 2,978-clause ordered core was
already LRAT-refuted in Lean as `Euler.Batch.C04.coreUnsat` with only
`propext`; the prior log and exact CNF/LRAT files are included.
The geometry-to-refutation bridge uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Independent witness validation

Each proposed short witness was located by exact ordered signed-list
comparison, without hashing or sorting literals. An independent
integer recipe reimplemented each relevant block and reproduced every
one of the 2,978 signed core clauses. The counts are:

| Clause family | Rows |
| --- | ---: |
| Support | 2,622 |
| Excess high | 165 |
| Degree pattern | 114 |
| Saturation | 27 |
| Pins | 26 |
| Lexicographic | 19 |
| Degree order | 3 |
| Anchors | 2 |

These are exactly the already exercised generic C02/C03 block types;
`ArchiveCoreBlocks.lean` is byte-identical to the C03-checked version.
Regeneration from the bundled compressed archive and core reproduced
all generated proof sources and signed recipes byte-for-byte.

## Checked proof

`C04RawFactored.lean` builds 64 signed chunks aligned to the loaded
core's conjunction tree, and checks an exact syntax identity with
that core. The 16 `C04CoreMembers*.lean` shards check
each short signed clause by local definitional equality inside the
actual geometric block, lifted through the generic membership lemmas.
`C04Linked.lean` combines this with the numbered valuation
transfer and the geometric reduction. The final target
`LatinGap.PairEncoding.C04Linked.allUsed_geometry_except_c04`
excludes C04 alone from the all-used size-17 reduction with the
existing linearity, saturation, minimum-degree-two, and all-low-pairs-used
hypotheses. It does not exclude the other all-used cases or establish
a packing threshold.

## Reproduction

Use Lean 4.36.0 and Mathlib revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. With the compiled
Euler geometry and Mathlib modules on `LEAN_PATH`, run
`./replay.sh` when a dedicated compiler slot is available.
It checks one source at a time at an interpreter cap of 2500 MB,
including a final independent import audit. Set `LEAN_BIN` if
needed, and set `REBUILD_CORE=1` to rebuild the prior SAT core
certificate from the bundled input, rather than reuse its compiled
module. No binary artifacts are included.

The kernel does not call Python. The following merely regenerates
the untrusted proposed local witnesses:

```sh
gzip -dc fixtures/EulerBatch/cases/04/original.cnf.gz > fixtures/EulerBatch/cases/04/original.cnf
CASE_DIR=fixtures/EulerBatch/cases/04 python3 plan.py
python3 verify-recipe-arithmetic.py
python3 gen-factored.py
```

Check packaged files with `sha256sum -c SHA256SUMS`.
