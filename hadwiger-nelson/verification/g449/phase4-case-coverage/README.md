# G449 non-four-colouring: bounded certificate pilot

Source: Heule and Przybocki, [From two heptagrams to a 449-vertex 5-chromatic unit-distance graph](https://arxiv.org/abs/2611.28518). Upstream commit 125bfda97ed1d336f84694de04dedcfb349c5164: [case generator](https://github.com/bprzybocki/G449/blob/125bfda97ed1d336f84694de04dedcfb349c5164/build.py), [proof stitching](https://github.com/bprzybocki/G449/blob/125bfda97ed1d336f84694de04dedcfb349c5164/stitch.py), [build invocation](https://github.com/bprzybocki/G449/blob/125bfda97ed1d336f84694de04dedcfb349c5164/verify.sh), [verification log](https://github.com/bprzybocki/G449/blob/125bfda97ed1d336f84694de04dedcfb349c5164/verify.log).

## What is reproducible upstream

The source bundles CaDiCaL 3.0.1 and dsr-trim 7aaed39, and constructs the exact same known base DIMACS (1,796 variables, 9,241 clauses; independent replay SHA-256 289d6b5d6922264a38075fc39ea42eab19044ff4b006a5c1b6fe475363bc2e62). It does not store the completed proof. The checker consumes one mixed LSR stream. First the 13,525-line DSR symmetry stage, converted to LSR, adds at-most-one clauses, triangular hints, a center-colour fixing, and blocked neighbourhood patterns with rotation/permutation substitution witnesses. Then six ordinary LRAT refutations are weakened by the negation of each case cube and stitched to this stream. The script rejects any negative RAT hint in these branch proofs. The final LRAT coverage step closes the remaining formula.

The logged 8,398 seconds and 73,305,873 case conflicts describe work, not exact proof bytes. No complete byte size is given. The smallest branch still had 322,711 conflicts; the last coverage step had 11,521.

## Smallest credible Lean route

1. Avoid implementing general LSR first. Work with proper four-colourings, already proved equivalent to this exact numbered base formula. Verify the concrete sevenfold vertex permutation maps the published edge list to itself and rotates the seven designated neighbours of the fixed central vertex.
2. Pick the center's colour as label 1 by a global palette permutation. Apply the checked finite coverage theorem to its seven neighbour labels (values 2–4). Instantiating the checked graph rotation and relabelling should put the translated proper colouring in one of the six exact branches. Check each branch's clause numbering, triangle hints, exclusions, and cube units in this interpretation. The original case files contain only the base formula, triangle hints, the exclusions for the specific case, and its cube units; all of the other DSR symmetry clauses can be avoided in this mathematical proof.
3. Generate and check the six separate LRAT refutations, each against its own independently generated clause list. A first feasibility gate is a bounded, independently checked sample from case 1; then assess checked proof size and memory before attempting the much larger branches. Importing an enormous proof as a monolithic kernel term may not work. A compiled checker or a native decision declaration is not an axiom-clean replacement for checking all six proofs; a chunked proof/state interface may be needed.
4. Glue these exact branch exclusions to the normalization theorem and to the already checked formula equivalence. The final upstream coverage-CNF replay should then be unnecessary.

## Checked in this pilot

The original Python witness generator recompiles a small finite table from the six published symbolic patterns and their exact exclusions. The Lean kernel, not the generator, checked all 2,187 supplied witnesses, the 53 admitted-pattern count, and the generic arithmetic soundness of the certificates. The theorem name is G449FiniteCoverage.orbit_case_coverage. It is a theorem about seven-neighbour words, not yet a graph-level theorem about a normalized proper colouring.

CertifiedG449.triangle_hint_of_proper separately derives the exact six-literal triangle hint used in the cases from pairwise distinct colours at the three vertices. Its only audited axioms are propext and Quot.sound. Coverage uses only standard Lean axioms, and no native decision declaration.

Reproduce with plain Lean 4.36.0: run python3 generate_coverage.py, then build FiniteCaseCoverage.lean. For TriangleHints.lean, expose the previous pilot's already-compiled FourColourCNF module on LEAN_PATH. No large proof was downloaded or run. This pilot does not prove the full base formula UNSAT, five-chromaticity, or a new plane bound.
