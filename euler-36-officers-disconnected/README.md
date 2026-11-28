# A lower bound for maximal arrangements of Euler's 36 officers

**Cite the author preprint:** Aafi Khan Malek (2026), *The minimum size of a maximal partial arrangement of Euler's 36 officers*. Zenodo. [DOI: 10.5281/zenodo.24624423](https://doi.org/10.5281/zenodo.24624423) · [BibTeX](CITATION.bib). This preprint is not a journal publication.

Euler asked whether all 36 officers can be placed in a 6×6 grid without repeating a rank or regiment in a row or column. The answer is negative. This note asks how few officers can be placed before every additional placement is blocked. [Dieter Betten's proof of the classical result](https://doi.org/10.1007/s00022-023-00669-3)

**The exact unrestricted minimum is 18.** The known upper witness is checked in Lean. The size-14 and size-15 exclusions, the [size-16 audit](verification/order16/), and the [complete size-17 audit](verification/order17-exact/) establish the lower bound using independently replayed SAT certificates. The size-17 audit covers 56 normalized formulas. The full lower bound is not yet Lean-verified.

[Exact result and proof (PDF)](paper/euler-36-officers-exact.pdf) · [LaTeX](paper/euler-36-officers-exact.tex) · [Complete reproduction audit](verification/order17-exact/)

[Earlier research note](paper/euler-36-officers-disconnected.pdf) · [LaTeX source](paper/euler-36-officers-disconnected.tex)

## Check the thirteen certificates

Use Python 3.10 or newer. Install the pinned CNF generator dependency and build DRAT-trim from its source. [DRAT-trim source at the checked commit](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985)

```sh
python -m pip install python-sat==1.8.dev24
python euler-36-officers-disconnected/verification/verify_certificates.py --checker /path/to/drat-trim
```

The verifier rebuilds each CNF, unpacks its trace, and requires `s VERIFIED`. The note proves why the thirteen formulas cover the cases claimed. The [Latin-square witness script](../orthogonal-latin-square-gap/verification/verify_witnesses.py) checks the 18-officer construction.

## Lean verification

The shared Lean project checks the 18-officer witness and proves the structural lower bound of 14 directly. Its two statements are `EulerOfficers.exists_maximal_eighteen` and `LatinGap.six_lower_bound`. Run `lake build` from the [Lean project](../orthogonal-latin-square-gap/lean/).

Lean's LRAT checker replayed the six certificates used to establish the 15-officer lower bound. The seven size-15 exclusions use the independent DRAT checker above. From the repository root, use the same Lean 4.36 toolchain as the shared project.

```sh
python euler-36-officers-disconnected/verification/verify_certificates.py --checker /path/to/drat-trim --lrat-dir /tmp/euler-lrat \
  --case q3-m1 --case q3-m2 --case q5-m2 --case q5-m3 \
  --case n6-f14-no_low --case n6-f14-wedge-fast
lean --run euler-36-officers-disconnected/verification/VerifyLrat.lean /tmp/euler-lrat q3-m1 q3-m2 q5-m2 q5-m3 n6-f14-no_low n6-f14-wedge-fast
```

Lean checks the unsatisfiability of the generated formulas. The reduction from partial arrangements to those formulas is proved in the paper.

OpenAI Codex assisted with the proof, computation, literature search, and note.

## Lean encoding link

The locally Lean-checked theorem [`LatinGap.PairEncoding.exists_seventeen_iff_clauses`](../orthogonal-latin-square-gap/lean/EulerPairClauses.lean) proves equivalence between the actual arrangement and the abstract finite pair/word clauses with an exact cardinality condition. The next checked modules establish the signed numeric variable mapping and the semantics of the sequential at-most-one support counters. The [prefix audit](verification/order17-lean-prefix) independently matches those formulas against 31,752 clauses of one exact archived size-17 CNF. This is not a Lean parser proof: the remaining 28,815 clauses of that CNF, the normalization into exact numbered cases, and their lower-bound certificates are not yet verified end to end in Lean.

The [cardinality audit](verification/order17-lean-cardinality) independently matches another 2,812 clauses of the same numbered case: exact projection count 17 and the four exact degree-excess counts of 5. Lean proves the rectangular sequential counter semantics and both specializations. The interpretation of the degree-threshold bits, remaining cuts and proof replay are still separate.

The [kernel-core pilot](verification/order17-lean-kernel-core) closes one extracted 2,646-clause core with standard Lean axiom `propext` only. A separate Python audit verifies that core’s containment in the archived 60,567-clause case. The number mapping to the full case and the remaining cases are not certified by that kernel theorem, so this is not yet a fully formal lower bound of 18.

The [full numbered pilot](verification/order17-lean-full-numbered) now checks containment and UNSAT of all 60,567 clauses of one exact archived size-17 branch in the Lean kernel. The included source, compressed original input, and certificate replay expose only `propext`. This proves the parsed numbered formula only; the byte parser, reduction from geometry to every numbered clause, are separate from this first pilot. Subsequent packages give complete numbered refutations for **13 of 56** size-17 formulas, still separate from the geometry link.

### All-low-pairs-used size-17 family

The [exact non-lex prefix](verification/order17-lean-allused-nonlex) now connects geometry to every archived pre-lex clause in this 17-formula family. Independent exact checks matched each signed row in order, for prefixes of 58,350 to 58,370 clauses. The [conditional final lex suffix](verification/order17-lean-allused-conditional-lex) checks the remaining 1,260 to 2,835 rows in each original and proves these clauses from adjacent free-label incidence ordering. The [full geometry-to-CNF theorem](verification/order17-lean-allused-full-geometry) now proves the simultaneous relabeling and combines both clause blocks. For any hypothetical geometric arrangement in this family, it gives a valuation of one of the 17 complete modeled CNFs. An independent exact audit matches each model to its original signed clauses with no gap. The byte parser, new refutations, and other geometric families are not part of this result; the global Lean lower bound remains incomplete.

The [conditional refutation composition](verification/order17-lean-allused-conditional-composition) verifies the general transfer and the exact list complement. An independent audit links 12 previously refuted formula declarations to their modeled clause lists row for row. This leaves five original refutations in the all-used family; the twelve exact containment or equality links must still be materialized in the Lean kernel. No new original refutation was added by this package.

The [complete C05 refutation](verification/order17-lean-c05) now verifies one more of the five originals not covered by the twelve-case package, bringing the all-used count to 13 of 17. Four SAT refutations remain in that family; the independent exact identity checks are not yet kernel equalities.
