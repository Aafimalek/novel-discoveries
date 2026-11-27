# Nine separated subset sums

**Proved lower bound:** Nine positive real weights whose 512 subset sums are pairwise separated by at least one have maximum **at least 149**. This supersedes the earlier 148 + 1/6 bound and answers the nine-weight instance of the lower-bound question in [Notik, §7, item 4](https://arxiv.org/abs/2611.17360). The classical upper-bound example has maximum 161. The exact real optimum in [149, 161] is still open here.

- [Manuscript and complete written proof (LaTeX)](paper/nine-separated-subset-sums.tex)
- [Exact arithmetic and example checks](verification/check.mjs): run `node nine-separated-subset-sums/verification/check.mjs` from the repository root.

The proof uses Harper's vertex-isoperimetric theorem and Borwein and Mossinghoff's published integer optimum. The script checks the explicit boundary count, rounding margin, and upper-bound example; it does not reprove either cited theorem. The full result is not yet formalized in Lean or peer reviewed.

Aafi Khan Malek, Independent researcher. Aafi selected and directed the project. ChatGPT assisted with the literature, proof development, manuscript, and verification code. Codex was not used.
