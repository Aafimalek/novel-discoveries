# Lean-checked asymmetric diagonal-gate criterion

The audited endpoint
\`WidthThree.Diagonal.Labels.balanced_of_diagonal_product\` finds a
balanced comparison between the distinguished a and an element of its
actual exclusive branch S. It uses exactly the earlier good-pair,
common prefix, branch labeling, and initial probability assumptions:

- a,b are incomparable, every strict predecessor of a lies below b,
  and the comparison count for a<b is at most half the total.
- S is the exclusive upset of b relative to a, including b itself,
  and is labeled by a common b-first ordered chain of length h >= 2
  followed by two rails X,Y. Either rail may be empty.
- Gates x_i < y_(i+d) and y_j < x_(j+e) hold wherever both endpoints
  exist; arbitrary extra cross relations are allowed. The condition is
  d*e <= (h-1)*(d+e), with no bound on the lengths of the two rails.

The conclusion is phrased in inclusive integer comparisons:
N <= 3 * count(a<z) <= 2*N. When n is the poset size, the counted
rankings are its linear extensions. This broadens the earlier checked
maximum-offset cap, but does not prove all width-three cases; it uses
no conditional XYZ result.

The main new reusable endpoint is
\`WidthThree.WeightedPool.weightedComparisonCount_of_branchRankSum\`.
It transfers a pointwise rank-sum inequality using fixed natural
weights p,q on two targets to the corresponding count inequality with
anchor weight p+q. The proof uses the previously checked antitone
cut decomposition on invariant finite rank fibers. It does not assume
independence or put equal weight on induced branch orders. The gate
application uses the transposed weights (e,d); strictness on the low
anchor bound gives the contradiction when d+e>0, including one zero
offset. Both zero offsets with two nonempty arms are impossible.

## Strict verification and dependencies

All six modules compiled serially with Lean 4.36.0 at
611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9 and Mathlib
fc4f59e577feb1a4956671bc04ac18aaaf8cd842 using
-j1 -M2450 -DwarningAsError=true in a writable overlay. The fresh
typed import confirms the exact inclusive theorem bounds and audits
the weighted count and first-high lemmas. All three endpoints depend
only on propext, Classical.choice, and Quot.sound; the weighted
finite-cut arithmetic uses only propext and Quot.sound. No warnings,
placeholders, or native evaluation occur in the verified run.

This is a delta over the existing checked joint-ranking, diagonal-head
and strict diagonal-anchor source packages. Their compiled objects and
pinned Mathlib must be on LEAN_PATH. The included DiagonalBalancedDraft
module is a verified, local callback refactor of the prior complete
assembly. The original checked source remains untouched and the
original max-offset theorem is retained here at its exact type.
See balanced-callback.patch. Put this overlay first on LEAN_PATH and
do not use a conflicting old DiagonalBalancedDraft object.

Set LEAN_BIN to the pinned executable and run ./replay.sh. Logs and
object digests from the completed strict run are included; objects
themselves are not included. The written proof and tiny independent
integer/closure diagnostic are supplemental.
