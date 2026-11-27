# Kernel replay for one complete size-17 Euler branch

`Euler.NumberedPilot.branchNoAssignment` proves that the full original
numbered DIMACS of branch `aus-0111_1012_1203_1320` has no satisfying
valuation. Its underlying formula contains **all 60,567 clauses** and
the original numbering of 10,646 variables. The byte-for-byte
archived input has SHA-256
`00b1bf0edffac4f5008c82475f22dff03a89dae040be0b268f2d6f28a63cea38`.

`FactoredCore.lean` proves the 2,646-clause pure-RUP core unsatisfiable,
using Mathlib’s explicit term generator and separate opaque kernel
theorems for individual proof steps. `EulerFullContainment.lean`
checks in Lean that every ordered core clause belongs to the original
parsed formula, using balanced formula and proof chunks. It then
transfers the empty-clause proof to the full original formula. The
final theorem and its inclusion and refutation lemmas use only
`propext`, not `native_decide` or `sorryAx`.

## Replay

With Lean 4.36.0 and the project's prebuilt Mathlib and dependencies
on `LEAN_PATH`, run `bash check_archive.sh`. It checks the archive
hashes, decompresses the exact archived input to a temporary
directory and builds both theorem files. The included core, LRAT
certificate and compressed input suffice, without a SAT solver.

The archive does not formally verify the DIMACS parser as a
byte-to-formula specification (it is used at elaboration to
produce concrete Lean formulas), derive the numbered clauses from
geometry, or cover any of the other 55 size-17 branches.

## Regenerate the core certificate

Start with the exact archived `original.cnf` and native branch
`native.drat` (SHA-256
`0bb921bea3b29331b0b34ae2592fd0b2402575e5439ce3251b35e6d2eaa7d3d1`).
With Kissat 4.0.4 and DRAT-trim
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`:

```sh
drat-trim original.cnf native.drat -c first.cnf -q
kissat --plain first.cnf first.drat             # UNSAT is exit 20
drat-trim first.cnf first.drat -U -c extracted.cnf -q
python restore_literal_order.py original.cnf extracted.cnf core.cnf
kissat --plain core.cnf core.drat               # UNSAT is exit 20
drat-trim core.cnf core.drat -U -L core.lrat -q
```

The restore step only returns each extracted clause to its literal
order in the input. It is untrusted preparation: Lean checks both
the fresh proof and the restored core’s containment. The final
certificate has 191 learned steps, 40,461 resolution steps, and
no RAT steps.
