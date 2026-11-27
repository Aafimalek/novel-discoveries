# A lower bound for maximal arrangements of Euler's 36 officers

Euler asked whether all 36 officers can be placed in a 6×6 grid without repeating a rank or regiment in a row or column. The answer is negative. This note asks how few officers can be placed before every additional placement is blocked. [Dieter Betten's proof of the classical result](https://doi.org/10.1007/s00022-023-00669-3)

The unrestricted minimum is now **17 or 18**. The original paper rules out 14 and 15 officers and proves the minimum is exactly 18 when the used-pair graph is disconnected. Its vertices are labels, and two labels are joined when they occur in the same placement. The later [size-16 audit](verification/order16/) rules out 16. The [degree-one audit](verification/order17-degree-one/) excludes all size-17 arrangements containing a label used once, using 27 normalized cases. A separate [degree-two audit](verification/order17-degree-two-high-double/) excludes three further normalized cases. Other degree-two cases are still open. These later computational exclusions have not been replayed in Lean.

[Research note](paper/euler-36-officers-disconnected.pdf) · [LaTeX source](paper/euler-36-officers-disconnected.tex)

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
