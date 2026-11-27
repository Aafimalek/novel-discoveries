# A balanced pair for a two-by-three branch in a poset

[Aafi Khan Malek's working note (PDF)](two-by-three-branch.pdf) states
and proves the restricted 2×3 branch theorem, with the exact integer
certificate table and the cutoff-model obstruction. The updated version
adds an explicit infinite width-three family, an extension-count proof,
and a comparison with related results. It does not
claim to settle the unrestricted width-three conjecture. This is
a repository research note, not a journal submission.

Run `python3 verify-certificate.py` to independently check the
25 rows on the 70 components, the 60 majority orders, and the
quarter rows and model obstruction. [Audit output](verified.log).
Run `python3 verify-example.py 50` to check the new example's exact
counts on 50 instances by a separate ideal dynamic program.
[Example audit output](verified-example.log). Compile the TeX twice with pdfLaTeX to resolve cross-references.
The [complete Lean proof and pinned replay](../verification/two-by-three-balanced)
are separate from the Python audit. The exact artifacts are indexed
by [SHA256SUMS](SHA256SUMS).
