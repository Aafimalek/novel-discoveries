# Checked six-row external packet certificate

Both modules passed strict Lean 4.36.0. This is a bounded proof
for the exact first packet of the base positive-anchor ES33 target.
It contains no solver call, trusted hash equality, placeholder proof,
or pre-assumed equivalence.

- `PacketTextPilot.lean` embeds the actual six external clause-body
  lines (`first-packet.rows`) with `include_str`. A checked axiom-free string
  equality binds a small ASCII character witness to
  those actual bytes. A separate small canonical parser splits LF
  lines and single-space signed decimal tokens, then calls the existing
  `TokenDocument.parse` for bound 37,365 and six rows. No pre-parsed
  integer result is substituted for text parsing.
- `PacketInternalPilot.lean` draws the prefix from the production
  `triples 32` enumeration, not a new dictionary. `List.take_append_drop`
  and `List.idxOf_append` transport closed computations on the first
  466 sign cells to exact production IDs 1, 2, 31, 466; no side
  dictionaries need reduction. It encodes the actual typed
  `packetRows` at labels 0,1,2,3. Ordered quartet membership places
  every row in `typedRows 32 7 7 6`. Proof-irrelevant scoping does not
  alter the signed row, so this gives exact clause membership in
  `compile … target32_covered`, not just similar logical meaning.
- The checked `parsed_packet_mem_internal` is closed: these embedded
  six raw text rows parse to the exact encoded packet list, and every
  row in that list occurs literally in the exact internal formula.
  It does not identify a normative external clause-loader object,
  prove a global row offset in Lean, match the rest of the file, or
  prove any satisfiability/unsatisfiability claim.

Static external slice replay on the existing reference and
independently emitted upstream files passed:

    python3 extract_first_packet.py /path/to/es32-anchor.cnf

This auxiliary Python check compares actual bytes at body rows
258385–258390 and tests the lexical shape; it is not the
Lean text theorem or proof of the full instance. A future certificate
loader must consume the same verified text chunks in order.

## Strict replay and audit

Use a fresh overlay with the exact matching `NumberedCNF` object and
the prior verified `ActualCoverage` + GoodRows + literal objects.
Compile `PacketTextPilot` (put `first-packet.rows` beside its source)
and then `PacketInternalPilot`, serially, pinned Lean 4.36.0, warnings
as errors, one worker, bounded wall time, 2250 MB Lean limit and
overlay TMPDIR. Verify all printed axioms against the standard three. In a fresh
overlay with `out/` and `tmp/`:

    python3 run_stage.py PacketTextPilot 35
    python3 run_stage.py PacketInternalPilot 52

The runner passes the path of the source as an absolute path, as needed
for `include_str` to read the adjacent fixture. Historical timings:
1.509s and 2.742s, peak 1,658,444 KiB reported child RSS. The audits show
only standard Lean axioms (and the exact string/witness equality is
axiom-free). The final proof handles only the six embedded rows, not
the checker-loaded full target or a conclusion about its UNSAT.
