# The first sizes above the Latin-square bound

A maximal pair of orthogonal partial Latin squares uses the same filled cells in two grids. The rows, columns, and ordered symbol pairs must satisfy the Latin and orthogonality rules. The pair is maximal when every additional filling would break a rule.

For order $n=3s$, the known bound is $F\ge 3s^2$, where $F$ counts filled cells. We prove two statements about the next sizes.

- For $s\ge2$, a maximal pair with $F=3s^2+1$ is impossible.
- For $s\ge3$, every maximal pair with $F=3s^2+2$ splits into three full orthogonal pairs of orders $s-1$, $s$, and $s+1$. The union of any three such pairs on disjoint label sets attains that size.

At order 12, the first two attainable sizes are 48 and 50. At order 18, the minimum lies between 111 and 114. The exact order-18 minimum remains open in this note.

Read the [proof note](paper/orthogonal-latin-square-gap.pdf) or its [LaTeX source](paper/orthogonal-latin-square-gap.tex).

## Lean verification

From this directory, run `cd lean` followed by `lake build` with the pinned Lean toolchain. [Lean source](lean/LatinGap.lean)

`LatinGap.no_plus_one` proves the one-cell exclusion for all orders covered by the note. `LatinGap.classify_plus_two` proves that every design at the two-cell threshold splits into three full orthogonal blocks. `LatinGap.plus_two_of_full_blocks` proves the converse.

[Aafimalek/latin-square-gap](https://github.com/Aafimalek/latin-square-gap) holds the same development in Lean's module format, with Challenge/Solution files that the Comparator tool checks, prepared for the Palomar registry.

## Check the finite examples

From the repository root, run the witness checker with Python 3.10 or later.

```sh
python orthogonal-latin-square-gap/verification/verify_witnesses.py
```

The script constructs the four examples and checks every pair projection and every potential insertion. The written proof establishes the general exclusions and classification.

## Prior work

The proof uses the matching inequality and the three-coordinate decomposition lemma of Donovan, Grannell, and Yazıcı. Their November preprint also classifies minimum pairs for large orders. [February 2026 preprint](https://arxiv.org/abs/2602.09908) · [November 2026 preprint](https://arxiv.org/abs/2611.13961)

Horak and Kim mention a manuscript in preparation by Horák, Meszka, and Rosa on the spectrum of attainable sizes. The public sources searched did not yield an earlier proof of the two statements above. [Horak and Kim, §1](https://arxiv.org/abs/2611.07117)

The proof, literature search, note, and checker were developed with AI assistance.
