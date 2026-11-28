# Forward endpoint-exclusion Lean replay

This package contains the exact source and receipts for the bounded
strict replay. Earlier checked modules still
separately supply the real witness, exact dictionary coverage, and P
from the actual chain-existence valuation.

## Minimal forward proof

1. `ES33.EndpointExclusionGeometry` retains `Ends.to_set` from the prior
   EndpointSubsets draft, building the selected finite image of the
   strict chain and using already checked selected-chain closure.
   It retains the median-of-groups and union/intersection parts of
   the EndpointPolygon draft, but omits all converse proofs and
   order-statistic reconstruction. Only two small local packet facts
   from EndpointMedian are needed; their source proofs are included.
2. If an opposite cap and cup share their distinct endpoints L,R,
   an interior point cannot be in both, since the sign of (L,x,R)
   would be both false and true. The union is even: for any selected
   sorted triple (a,b,c) the sign equals the color of its median b,
   defined as the sign of (L,b,R). Inside a color this follows from
   chain homogeneity; across colors the two packet facts move the
   signs to the matching median. Each quartet's first two signs
   match, and its last two signs match. The union's size is
   s+t−2 by the exact two-element intersection. Thus s+t=9
   yields an even seven-set, without making any convexity claim
   about an arbitrary, unrealized signotope.
3. `RealChainExclusions` consumes checked signotope and residual
   avoidance as packaged in `Residual32`. For a cap of length seven
   use the trivial length-two cup on its endpoints to get the same
   even seven-set. A cup of length six gives an all-positive size-six
   set, forbidden by the normalized anchor. The cross cases use the
   opposite-chain union above. All three contradictions concern the
   **same** `chainVal` whose P was already checked.
4. The top-level connectors give an internal numbered
   satisfiability witness for each real 33-point counterexample, and
   therefore the classical ES33 claim **conditional on UNSAT of that
   exact internal object**. No reverse abstract implication is claimed or
   needed. No target UNSAT, lex formula, external DIMACS linkage, or
   certificate is asserted.

## Strict verification order

Use the same pinned Lean 4.36.0 one-worker/warnings-as-errors replay
as the earlier connector. Reuse the receipts from
`es33-real-chain-valuation-check/release`,
`es33-whole-coverage-check/release`, and
`es33-residual-extraction-check/release`. Create a fresh overlay
`out/ES33/` with read-only symlinks to the **full** fresh
`es33-real-chain-valuation-check/out/ES33/` object closure: Lean picks
the first search path with the ES33 namespace. Include compiled
non-namespaced valuation, literal, numbering, real-witness and coverage
objects and exact Mathlib paths from the corresponding checked runners.
Compile `ES33.EndpointExclusionGeometry` first and retain its four
axiom audits; only then compile `RealChainExclusions` and retain its
three audits. With the preparatory links in place, in a fresh overlay run:

    python run_stage.py ES33/EndpointExclusionGeometry 65
    python run_stage.py RealChainExclusions 75

The runner checks prior receipt hashes and pins the Lean executable; its
single worker uses warnings as errors, 2250MB Lean and 2310000KiB sampled
RSS caps, plus overlay TMPDIR. The independently audited external
DIMACS byte/multiset relation still needs its own formal exact-object
link (or sufficient one-way checker-row containment).
