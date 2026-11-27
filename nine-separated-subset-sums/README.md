# Nine separated subset sums

**Result:** Nine positive real weights whose 512 subset sums are separated by at least one must have maximum at least **148 + 1/6**. This improves the published bandwidth bound of 148. It does not reach 149; the exact optimum remains unknown to us.

- [Research paper and full written proof (LaTeX)](paper/nine-separated-subset-sums.tex)
- [Exact arithmetic and example checks](verification/check.mjs): run `node nine-separated-subset-sums/verification/check.mjs` from the repository root.

The proof uses the classical bandwidth of the nine-cube and Borwein and Mossinghoff's published integer optimum. The script verifies the constants and the upper-bound example, not those two inputs or the full real optimization. No Lean proof is included yet.

Aafi Khan Malek, Independent researcher. Aafi selected and directed the project. ChatGPT assisted with research, argument development, writing, and the verification script. Codex was not used.
