# Explicit finite ambient realization of the switched ladder

The associated written [pairwise gate theorem](pairwise-gates.md)
provides a switched branch with no fixed-product-cap labeling. Here is a
concrete ambient instance, with non-isolated distinguished element.
Take \(n=10,\ m=4,\ h=2\). On the 24 labels
\[
 a,a',b,q,\ x_0,\ldots,x_9,\ y_0,\ldots,y_9
\]
take the transitive closure of these strict edges, and **no others**:

1. \(b<q\), \(q<x_0\), \(q<y_0\), the two successive rail orders;
2. \(x_i<y_{i+1}\) for \(i=0,1,2,3\), \(x_4<y_6\),
   \(y_2<x_4\), and \(y_j<x_{j+1}\) for \(j=4,5,6,7,8\);
3. \(a<a'\) and \(b<a'\).

The rail edges increase the index, the prefix only enters the rails,
and \(a'\) has no successors, so there is no directed cycle. Neither
extra edge into \(a'\) forces any other comparison. The two incomparable
minima are \(a,b\), so the strict predecessor assumption on \(a\) is
vacuous; \(U(a)=\{a'\}\), while \(U(b)=\{a',q\}\cup X\cup Y\).
Consequently the exclusive branch is **exactly** the 22 labels
\(\{b,q\}\cup X\cup Y\) with the intended ordinal prefix and switched tail.

For each fixed linear extension of these 22 branch labels, \(a'\) may
be inserted after any number \(k=1,\ldots,22\) of branch labels. The
admissible positions for \(a\) are its \(k+1\) slots before \(a'\);
exactly one precedes \(b\). This decomposition is a bijective count
of full extensions, not a relative-order independence assumption.
There are 22 full extensions with \(a<b\) per branch order and
\(\sum_{k=1}^{22}(k+1)=275\) full extensions in that same fiber, so
\(\Pr(a<b)=22/275=2/25<1/2\).

The two rail chains with the prefix on one and the exterior chain
\(a<a'\) cover the poset. The antichain \(a,x_0,y_0\) shows width
exactly three. Indeed \(a',x_1,y_1\) is a second disjoint antichain.
The branch passes the written pairwise test. The fixed gates require
\(d\ge5,e\ge4\), violating \(de\le d+e\); connectivity of the branch
incomparability graph ensures no alternate two-chain cover removes
this obstruction. This comparison concerns the same good pair and
branch only. The ambient instance has three maximal elements and
does not claim to escape the [known v23 preprint's three-maxima result](https://zenodo.org/records/24357683),
or any other ambient class. This finite realization and new arithmetic
draft are not themselves Lean-verified.
