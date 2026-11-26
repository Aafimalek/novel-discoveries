# A lower bound for maximal arrangements of Euler's 36 officers

Euler asked whether all 36 officers can be placed in a 6×6 grid without repeating a rank or regiment in a row or column. The answer is negative. This note asks how few officers can be placed before every additional placement is blocked. [Dieter Betten's proof of the classical result](https://doi.org/10.1007/s00022-023-00669-3)

We rule out all maximal arrangements with 14 officers, bringing the unrestricted minimum into the interval **15–18**. We also prove that the minimum is exactly **18** when the used-pair graph is disconnected. Its vertices are labels, and two labels are joined when they occur in the same placement. The unrestricted cases 15, 16, and 17 remain open in this note.

[Research note](paper/euler-36-officers-disconnected.pdf) · [LaTeX source](paper/euler-36-officers-disconnected.tex)

## Check the six certificates

Use Python 3.10 or newer. Install the pinned CNF generator dependency and build DRAT-trim from its source. [DRAT-trim source at the checked commit](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985)

```sh
python -m pip install python-sat==1.8.dev24
python euler-36-officers-disconnected/verification/verify_certificates.py --checker /path/to/drat-trim
```

The verifier rebuilds each CNF, unpacks its trace, and requires `s VERIFIED`. The note proves why the six formulas cover the cases claimed. The [Latin-square witness script](../orthogonal-latin-square-gap/verification/verify_witnesses.py) checks the 18-officer construction.

## Lean verification

The shared Lean project checks the 18-officer witness and proves the structural lower bound of 14 directly. Its two statements are `EulerOfficers.exists_maximal_eighteen` and `LatinGap.six_lower_bound`. Run `lake build` from the [Lean project](../orthogonal-latin-square-gap/lean/).

Lean's LRAT checker can also replay all six SAT certificates. From the repository root, use the same Lean 4.36 toolchain as the shared project.

```sh
python euler-36-officers-disconnected/verification/verify_certificates.py --checker /path/to/drat-trim --lrat-dir /tmp/euler-lrat
lean --run euler-36-officers-disconnected/verification/VerifyLrat.lean /tmp/euler-lrat q3-m1 q3-m2 q5-m2 q5-m3 n6-f14-no_low n6-f14-wedge-fast
```

Lean checks the unsatisfiability of the generated formulas. The reduction from partial arrangements to those formulas is proved in the paper.

OpenAI Codex assisted with the proof, computation, literature search, and note.
