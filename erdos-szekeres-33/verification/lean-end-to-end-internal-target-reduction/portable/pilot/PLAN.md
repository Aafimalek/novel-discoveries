# Bounded next target: exact external packet ↔ internal six rows

The included bytes `first-packet.rows` are the six clauses at
**1-based body rows 258385 through 258390** of the unaugmented
`etv_signotope(7,7,6,32)` sandbox fixture, whose header is
`p cnf 37365 474144`. They are the packet for labels (0,1,2,3).
`extract_first_packet.py PATH` verifies the exact slice bytes and
strictly checks its lexical shape. This has passed on the sandbox file;
it does not by itself identify the full external file in Lean.

## Small kernel-only proof design

1. Embed the six raw lines as a String. Use the exact canonical
   lexical grammar demonstrated by the file: decimal signed integer
   tokens separated by one space; each line ends in one terminal
   zero and LF. Parse String→integer rows without trusting a generated
   list of already-parsed clauses, then apply the existing proved
   `TokenDocument.parse` with number bound 37365 and chunk clause
   count 6. Prove the concrete six-row result with small kernel
   reduction, not `native_decide`. The proof is about the embedded
   bytes and this frontend, not all syntactically valid DIMACS files.
2. Form the internal typed `packetRows` directly at Fin32 labels
   (0,1,2,3). Use the actual dictionary, not an alternate numbering.
   Its four sign variables have IDs 1, 2, 31, and 466: (0,1,2) and
   (0,1,3) are first two; (0,2,3) follows the 30 (0,1,*) triples;
   (1,2,3) follows the 465 first-label-zero triples. Prove these from
   production order using `List.idxOf_append` (sign list first,
   two side dictionaries never reached), local cuts of the Fin
   ranges, and closed kernel computation only for the ≤466 sign
   prefixes/counts. This avoids evaluating every variable lookup
   across the 37,365-cell table or the entire target CNF.
3. Show equality of the parsed six-row list and
   `encode (fun k => (dictionary 32 7 6).idxOf k + 1)
     (packetRows (0 : Fin 32) 1 2 3)`.
   Show the typed packet block actually occurs in `typedRows` using
   strictly ordered quartet membership and the last flatMap family.
   A generic proof-irrelevant erasure of the support scoping in
   `compile` converts this to an exact membership / `Matches`
   statement for these six checked rows in the same internal
   numbered formula. Do not claim the Lean formula's global row
   offset until its prefix counts have separately been proved.

## Expansion without a hash-equality premise

For a later whole-file link, have the actual external certificate
frontend consume the exact text chunk sequence, in order, with the
declared original header and computed total row count. Compare each
parsed chunk to the corresponding internal chunk with kernel-backed
proofs; compose by the append/concat lemma for exact equality, or
the `Matches checkerFormula compiledTarget` direction for UNSAT
(if chunks duplicate/permutate literals or rows). A mere checksum
or agreement on counts is not a theorem about the loaded clauses.
The published external file must be the same byte stream consumed
by this parser, not a freshly generated proxy identified only by hash.

Start with the isolated six-row proof before any 474,144-row attempt.
The future full rank lookup and certificate-loader integration are
separate tasks. This plan does not include UNSAT or a certificate.
