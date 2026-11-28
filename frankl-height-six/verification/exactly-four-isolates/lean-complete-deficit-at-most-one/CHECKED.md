# Checked exact-four / maximum source deficit at most one

Main endpoint:
`FranklForcingFiber.exact_four_not_multiple_sources_of_deficit_le_one`.
Its hypotheses are actual NoStrictMajority and WeakMinimalGround,
exactly four isolated points, at least two source stars, and
`∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2`.
Conclusion: False. This is **not** a global bound on source deficit or
an exclusion of higher deficits. It does not finish all exactly-four
families or Frankl height six.

The unique-triple proof handles no outsider by 12 vs. 11 and any
outsider by four actual mixed isolate omissions at every source.
For a source in the triple, the two raw co-isolates come from one
inside block and one cross pair; for an outside source they come
from two different cross pairs. Full raw isolate support and each
co-isolate follow independently from a k+1-coordinate linked quotient.

The assembly separately uses the already checked all-ordinary branch
(no triples), the new single-triple contradiction, and the separately
checked many-triples contradiction. The four new modules replayed in
the same pinned Lean 4.36, Mathlib, one worker, 2500 MB, Werror, and
workspace overlay; replay does not claim a fresh transitive rebuild.
