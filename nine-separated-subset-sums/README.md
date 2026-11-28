# Nine separated subset sums

**Proved and checked end to end in Lean:** Nine positive real weights whose 512 labeled subset sums are pairwise separated by at least one have maximum **at least 149**. The classical upper-bound example has maximum **161**. The exact real optimum in [149, 161] remains open.

- [Written proof (PDF)](paper/nine-separated-subset-sums.pdf) · [LaTeX source](paper/nine-separated-subset-sums.tex)
- [Full Lean theorem, audit, and source replay](https://github.com/Aafimalek/novel-discoveries/tree/76beffd491584923083c1c3d8f2abe637dde12a3/nine-separated-subset-sums/verification/lean-real-149)
- [Exact arithmetic and example checks](verification/check.mjs): run `node nine-separated-subset-sums/verification/check.mjs` from the repository root.

The bound answers the nine-weight instance of the question in [Notik, §7, problem 4](https://arxiv.org/abs/2611.17360). The written proof cites the published integer optimum. The separate Lean proof checks the real-to-integer reduction and every integer exclusion needed for 149. Its axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`. The full source archive is available for a clean rebuild; the checked development was run in the pinned workspace. The paper has not been peer reviewed.

Aafi Khan Malek, independent researcher, Ahmedabad, India. Aafi selected and directed the project. ChatGPT assisted with the literature, proof development, manuscript, and verification code. Codex was not used.
