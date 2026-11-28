# Verified labeled-trace bridge

FranklFourTraceMaskBridge.lean compiled cleanly with pinned Lean
4.36.0 / Mathlib, one worker, a 2500 MB Lean cap, and an overlay
TMPDIR. The successful replay exited zero in about 2.4 seconds
with no warnings or errors. Its 11 public theorem audits all
list only propext, Classical.choice, and Quot.sound.

The bridge proves exact bit membership, decoding of union and
strict inclusion, symbolic packing of any labeled family that
contains the mandatory traces, duplicate-free cardinalities and
frequencies, numeric eligibility, and exact safe-support
membership/cardinality and containment in a witness chain's
bottom. It imports the existing checked numeric definition;
it does not enumerate arbitrary families again.

See replay.log and SHA256SUMS for exact records.

Unchecked here: the transfer from arbitrary ambient points
to four isolate labels and the actual-family avoidance size /
chain argument. This module is not the full five-isolate theorem.

For a portable replay, first compile
`FranklFourTraceCertificateDefinitions.lean` from the
[companion classifier](../lean-trace-classifier), add the resulting
module and the pinned Mathlib build to `LEAN_PATH`, then run:

    lean -j1 -M2500 -o FranklFourTraceMaskBridge.olean FranklFourTraceMaskBridge.lean
