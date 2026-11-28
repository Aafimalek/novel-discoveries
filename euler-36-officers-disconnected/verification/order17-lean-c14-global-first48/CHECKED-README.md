# C14 stable shared global index, bounded pilot
The definitions carry exact clauses for all 13,910 slots, but data compilation
is not proof of corresponding learned clauses. Scope and checked endpoints,
if proved, are reported by the audit. No geometry or terminal-empty theorem.

Raw archived DIMACS SHA-256
1250abf3c7bab4709e3c5d22c4c57b0beb833052bf308092690668e7346ceb50;
raw sorted LRAT SHA-256
bc70268e380895a051d8a6c2b354a3af0dd39318d2e4595b321563d85257b101.
Source rows use fixed lookup Euler.C14.Production.rowAt; the same
constant supplies the conclusion and hypotheses of each conditional
slice. The linked first24 local-packing result from a different module
does not automatically transfer to this complete global prefix.

Use ./replay-portable.sh with absolute LEAN_BIN and a pinned colon
separated LEAN_MATHLIB_PATH. Exact expected module ordering is
checked-order.txt; sources use ordinary kernel checking, one Lean 4.36
worker, memory cap 2450 MB, warning-as-error, scratch TMPDIR. Build .olean
files are not redistributed; fresh ones must match the specified Lean
and Mathlib versions. Incremental local receipts are valid only for the
frozen source and dependency closure: invalidate downstream objects if
any input object or source changes.

All 33 new modules passed; the imported generic source was already checked
and is included for a fresh replay. Checked conditional endpoints:
- Euler.C14.Production.first: Slice base rowAt 8825 8849,
  24 actual additions IDs 10716..10739 (263 hints).
- Euler.C14.Production.second: Slice base rowAt 8849 8873,
  24 actual additions IDs 10740..10763 (478 hints).
- Euler.C14.Production.first48: Slice base rowAt 8825 8873,
  for arbitrary base; composed with the identical rowAt constant.
Each axiom audit reports propext. This package proves neither the original
global prefix GoodBelow base rowAt 8825 nor the archived CNF UNSAT.
