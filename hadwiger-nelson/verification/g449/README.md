# G449 verification pilot: exact cyclotomic geometry

This is an independent calibration using Marijn J. H. Heule and Benjamin Przybocki's [G449](https://github.com/bprzybocki/G449), the graph from [From two heptagrams to a 449-vertex 5-chromatic unit-distance graph](https://arxiv.org/abs/2611.28518). The graph, its coordinate data, and the original chromatic result are theirs. This pilot makes no novelty claim for the graph and does not change the unrestricted Hadwiger–Nelson bounds.

The independent pure-Python verifier uses integer Laurent polynomial multiplication followed by reduction modulo Φ42, the minimal polynomial of the chosen primitive root. The coordinate denominator is the upstream value 49. Over the pinned data, the verifier regenerated all 2,198 unit edges from 100,576 unordered pairs, matched the independently parsed sparse6 list, counted 483 triangles and 49 unoriented unit directions, and verified the supplied proper five-coloring. It regenerated the plain four-color CNF (1,796 variables, 9,241 clauses).

The authors document a streamed LSR refutation of that four-color formula in their [verification log](https://github.com/bprzybocki/G449/blob/125bfda97ed1d336f84694de04dedcfb349c5164/verify.log). The recorded run took about 8,398 seconds. This pilot did not rerun the refutation or verify it in Lean. A proper five-coloring alone establishes an upper bound, not five-chromaticity.

## Reproduce

Upstream data are not redistributed in this package. Obtain both files from the pinned commit:

```sh
source=https://raw.githubusercontent.com/bprzybocki/G449/125bfda97ed1d336f84694de04dedcfb349c5164
curl -fsS "$source/G449.k21" -o G449.k21
curl -fsS "$source/G449.s6" -o G449.s6
python3 replay.py --sparse6 G449.s6 --cnf replay-base.cnf --edges-json edges.json
sha256sum G449.k21 G449.s6 replay-base.cnf
python3 generate.py
```

Expected SHA-256 digests:

```text
58a45c4e653ff63e0218e1dec988e0a532905969dda3fc7bf84a3c83874a3848  G449.k21
0db89dfb231a2722cb54a5bc3ce9e27afc672e73bd1230c41e08845b449e1b21  G449.s6
289d6b5d6922264a38075fc39ea42eab19044ff4b006a5c1b6fe475363bc2e62  replay-base.cnf
```

## Lean scope

Using Lean 4.36.0 and Mathlib, compile `CyclotomicWitness.lean`, generated `G449Data.lean`, then `G449OneDirection.lean`, `G449Direction1.lean`, generated `G449SampleRows.lean`, and `G449TwoEdges.lean`. Expose the directory on `LEAN_PATH` when using `lean -o` directly. The checked general theorem `dist_one_of_normCoeffs` proves that the integer coefficient check implies unit distance in the Euclidean plane. It derives the polynomial identity for the chosen primitive root, verifies evaluation against a checked power-reduction table, and connects complex conjugation to Euclidean distance. The Lean calibration verifies the whole power table and two actual G449 edges, from zero-based original rows (0,1) and (0,8). The second edge uses eleven nonzero difference coefficients. The statements refer to the supplied endpoints generated from the pinned artifact rather than only their translated directions. Only Lean's three standard axioms occur in the geometry theorem, and the finite checks use only standard axioms, without native decision.

This is not an all-edge Lean formalization. The remaining steps are to check all 49 direction norms and every edge-to-direction index in Lean, connect the bare numeric CNF to Lean's coloring predicate, and independently formalize or reconstruct a proof of unsatisfiability from a certificate. The original LSR proof can use proof rules not provided by the simple one-case LRAT path; do not treat upstream `lsr-check` or Python output as kernel verification.

### Prime-seven direction catalogue and extension checks

The [prime-seven package](prime-seven-catalogue) gives a four-color obstruction for prime-to-seven directions, checked in Lean in the polynomial-witness model, and a complete handwritten classification of norm-one directions with power-of-seven denominators. The exact audit checks the two catalogues and supplies five-colorings for every one-point extension of G449 in its denominator-seven grid, including the 34 exceptions to the supplied coloring. This does not change the 6–7 plane bounds.
