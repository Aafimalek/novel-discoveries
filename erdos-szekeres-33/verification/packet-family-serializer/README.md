# Checked scalable packet-family and canonical serializer

The packet-family theorem module passed strict pinned Lean replay.
This is a generic proof for **all packet rows**, not a new fixed handful. Other row families
and the external byte-loader link still require separate Lean proofs.

## Checked full packet-family hinge

`PacketFamilySerializer.lean` imports the verified production sign rank
and whole dictionary coverage. It constructs an executable six-row
serializer given any ordered quartet: IDs come from the orientation
rank formula, not from scanning the full dictionary. Its proof applies
the checked production quartet input guards and the rank theorem at
the four references. It preserves literal order and row order exactly,
including all six polarities. A flatMap/map congruence lifts this to:

    encode productionId (typed packet family) = fastPacketFamily n
    compile dictionary allTyped covered = encode productionId pastRows ++ fastPacketFamily n

These statements are generic in n, K, A, B, taking only the appropriate
coverage proof. The same generic proof attachment erasure used by the
checked 24-row block is made public. `packet_token_roundtrip` proves
round-trip for the entire packet suffix emitted with the actual
variable bound, by previously checked signed literal legality. The
canonical text renderer is also specified: ASCII signed decimal words,
single spaces, terminal zero and LF. The theorem also factors this
internal rendered string at the packet boundary. The external text
parsing layer is not proven by
the token-layer theorem. Nothing evaluates 215,760 rows inside Lean
to prove the generic hinge.

## Side numbering, exact guards and sizes

`SideRankSpec.lean` defines executable pair and triple rank formulas
and isolates two exact side hinge propositions without asserting them.
The side block weights on increasing labels are:

    pair(a,c)     = max(0, min(L,c-a+1) - 1)
    triple(a,b,c) = max(0, min(L,width3(side,a,b,c)) - 3)

For each side the pair block precedes the triple block. Pair keys start
at length 2, triple keys at length 4; the within-block offsets are
d−2 and d−4. Cup begins after the entire cap dictionary; cap begins
after all signs. Length-three chain-state literals do not allocate a
fresh side key: negative orientation sign for caps, positive for cups.
Pair length three is not aliased. Prefix sums use actual finite label
intervals; the eventual proof repeats the weighted block split
(nonmembership of earlier labels/families + idxOf append), proves the
inclusive length range, and separately accounts for the preceding
whole sign/cap sizes. Required domain guards are in the exact stated
`PairIdsCorrect` and `TripleIdsCorrect` goals.

## Exact external byte evidence, separate from Lean

Run `python3 replay_arithmetic_stream.py EXTERNAL_FILE`. This streams
an independent closed-form sign rank and cached side weight prefixes,
emits all four row blocks, and compares the actual external header,
every raw ordered DIMACS row, and EOF. It needs neither a digest
equality nor a second copy of the output in RAM. It matched both the
reference file and the independently emitted upstream copy byte for
byte: **474,144 rows, 37,365 variables**. At n=32 the dictionary
lengths are 4,960 signs, 2,531 cap pairs, 15,485 cap triples, 2,180
cup pairs, 12,209 cup triples. Body row blocks are 141,908 cap,
114,557 cup, 1,919 cross, and **215,760 packets**, starting at
1-based body row 258,385 and extending to EOF. See the receipt.
That exact byte comparison is a computational check, not a Lean
theorem about the checker-loaded file.

## Remaining steps in a scalable exact external proof

1. Prove the two side rank hinges and exact encoder identities for
   cap/cup/cross. Reuse the current
   production row constructors rather than reasserting hand-written
   formats. The formal result from this package concerns packet-only.
2. Prove canonical text serialization/parsing commutes with token
   emission, as a string/byte theorem. Use decimal-word inversion
   (including minus polarity and zero rules), line-list inversion,
   and header/body composition. The checked 24-row example supplies
   a small frontend sanity test, not the induction. For throughput,
   use stronger cursor-based raw-byte parser or bounded blocks
   instead of elaborating a single enormous character literal.
3. A checker must consume the **same** canonical text stream or its
   formally parsed chunks. Need equality or the sufficient direction
   `Matches checkerRows compiledTarget` for the entire input.
   Verifying chunk partition/concatenation and exact headers is
   separate from proving each typed family hinge. Replaying the
   arithmetic byte comparator helps pin the observed artifact, but
   it does not replace Lean equality to the checker-loaded object.
   The exact numeric packet starting offset is also presently an
   external observation, not the generic Lean suffix theorem.
4. No SAT search, UNSAT certificate, Hadwiger–Nelson conclusion,
   or ES33 verdict follows from formula identity alone.

## Strict replay

In a fresh overlay with out/ and tmp/ and the pinned historical objects
available in the original workspace:

    python3 run_stage.py PacketFamilySerializer 70
    python3 run_stage.py SideRankSpec 50

Lean 4.36.0, warnings as errors, one worker, 2250MB internal memory
limit, 2310000KiB sampled RSS guard and overlay TMPDIR. No geometry
objects or theorem-to-file identity assumptions are imported. The
SideRankSpec check is a syntax/type check of definitions and explicitly
stated goals, not a proof of those goals.
