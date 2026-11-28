# Checked four-packet / 24-row contiguous bridge

Both modules passed strict pinned Lean 4.36.0. The staged fixture is exactly
the 24 canonical LF-terminated DIMACS body rows 258385 through 258408
(1-based, excluding the header) of the reference anchored ES33 target
and an independently generated upstream copy. The byte slice matched
both files with `python3 extract_first_four.py FILE`, with no hash
comparison substituting for content. This external slice audit alone
is not a theorem about a complete checker-loaded object.

## Exact checked statements

- `Packet24Text.lean`: use `include_str` to read the raw 276-byte
  adjacent fixture, then prove that its character witness represents
  that exact string. It reuses the already checked six-row pilot's
  canonical text parser and computes the lexical/TokenDocument parse
  for all 24 lines. It does not accept a pre-parsed integer row list
  as input or use a native oracle.
- `Packet24Internal.lean`: compute the actual first four ordered
  quartets, (0,1,2,3) through (0,1,2,6), from the production packet
  list. Compute the nine new IDs through a prefix of 469 actual
  sign-table entries and reuse the previous four checked ID theorems.
  The cap and cup dictionaries do not participate in these lookups.
- `scope_encode` erases the compiler's proof attachments and
  preserves the exact order and signed literals. A take/drop
  identity for the production packets and the generic distributivity
  of encoding over append give the literal contiguous factorization
  `compiled = encoded_pre ++ (parsed24 ++ encoded_post)`.
  Thus each parsed external row occurs with exact literal order in
  the internal CNF: the direction needed for UNSAT transport. The
  theorem does not claim an internal numeric global row index.
- This is a larger bounded prototype, not a proof about the full
  signotope family or entire DIMACS file. To scale, keep the generic
  append/encoding and scope lemmas, parameterize offset/count cuts,
  and prove canonical rank or narrower prefix facts for each chunk.
  Full text identity requires the checker loader to consume the
  exact verified chunk sequence and header. Unknown SAT/UNSAT status
  is unchanged.

## Strict replay

Check SHA256SUMS for source identity only; then in a fresh overlay
rebuild serially with the already accepted pinned objects. The
dependency order is `PacketTextPilot` and `PacketInternalPilot` as
the previous verified dependencies, then `Packet24Text`, then
`Packet24Internal`. Include the previous coverage/GoodRows/literal
and NumberedCNF object roots. Invoke Lean 4.36.0 with absolute source
paths (needed by `include_str`), one worker, strict warnings, overlay
TMPDIR and bounded memory/time. Preserve the printed axiom reports.
Audit receipts show 7.777s (text) and 5.134s (internal), with a reported
peak 1,836,856 KiB, exit zero and only standard Lean axioms or subsets.
The exact raw string-to-character equality uses no axioms.

With the verified prerequisite objects still available in the original
workspace, in a fresh overlay having `out/`, `tmp/`, source and fixture:

    python3 run_stage.py Packet24Text 35
    python3 run_stage.py Packet24Internal 52

A pass concerns the actual embedded 24 lines only, not the full file.
