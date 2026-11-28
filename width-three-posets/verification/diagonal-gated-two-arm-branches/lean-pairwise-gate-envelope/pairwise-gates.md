# Pairwise gate budgets for intertwined branches

This is a written structural extension of the Lean-checked weighted
diagonal criterion. It uses the verified actual-ranking weighted-count
theorem and fixed-anchor selection, but the present structural extension
is **not Lean-checked**. It is not a result for all width-three posets or
a literature-wide novelty claim.

## The local-budget theorem

Let \(P\) be finite. Fix incomparable \(a,b\), every strict predecessor of
\(a\) strictly below \(b\), with \(\Pr(a<b)\le 1/2\) over uniform linear
extensions. Let \(S=\{b\}\cup(U(b)\setminus U(a))\), where \(U\) is strict
upset. Suppose \(S\) is the ordinal sum of a chain of length \(h\ge2\)
starting at \(b\) and a tail partitioned into increasing chains
\(X=(x_0,\ldots,x_{r-1})\), \(Y=(y_0,\ldots,y_{t-1})\).
No common uniform gate offsets are assumed. Allow additional cross
relations and either rail to be empty.

For each \(i,j\) define
\[
 u_i=\min\bigl(\{k<t:x_i<y_k\}\cup\{t\}\bigr),
 \qquad
 v_j=\min\bigl(\{k<r:y_j<x_k\}\cup\{r\}\bigr).
\]
For an incomparable pair \(x_i\parallel y_j\), put
\[
 A=u_i-j,\qquad B=v_j-i,\qquad M=\max(\min(i,j),|i-j|),\qquad c=h-1.
\]
Here \(A,B>0\): for example \(u_i\le j\) would provide an actual
successor at an index at most \(j\), forcing \(x_i<y_j\). The sentinel
\(u_i=t\) is permitted and also exceeds \(j\). The argument for \(B\)
is symmetric.

**Theorem.** If every incomparable pair \(x_i,y_j\) satisfies
\[
                   AB\le(c+M)(A+B),                    \tag{1}
\]
there is a balanced comparison between \(a\) and an element of its
exclusive branch. Equivalently, if the branch has no such balanced
comparison, at least one incomparable cross pair violates (1), namely
the two first-high labels.

Only the new two-high obstruction needs proof. Apply the checked
first-high case assembly to this same branch: if no comparison with
\(a\) is balanced, the common prefix is low, the both-all-low and
exactly-one-high cases are impossible, and both rails have first highs
\(x_i,y_j\). A low comparison has probability strictly below \(1/3\);
a high one has probability strictly above \(2/3\). These cutoffs are
equivalently integer comparisons with the total number of extensions.
Empty rails are already covered by the checked all-low/one-high cases.

Put \(C=h+i+j+1\). In an actual induced branch ranking \(R\), the earlier
head has rank at most \(C\): every tail label preceding it is in one
of the two low prefixes. If the heads were comparable, the earlier
one in the poset would have this bound in **every** ranking. The two
fixed low anchors \(\ell_1,\ell_2\) from the checked selection theorem
satisfy
\[
 D_R=\rho_R(\ell_1)+\rho_R(\ell_2)
 \ge 2h+i+j+M=C+c+M .
\]
By single-target pooling the early comparable head could not be high.
Therefore the first heads are incomparable.

The rank of \(x_i\) is at most \(h+i+u_i+1=C+A\), because any Y label
at or beyond the first successor cannot be before it, and the
sentinel permits all \(t\) labels only when that is the available
bound. Similarly \(\rho_R(y_j)\le C+B\). Choose the head weights
\((B,A)\), fixed **after** selecting the first-high indices \(i,j\)
and **before** quantifying over \(R\). For either order of the heads,
the weighted sum is bounded by
\[
 B\,\rho_R(x_i)+A\,\rho_R(y_j)\le (A+B)C+AB\le (A+B)D_R.
\]
Indeed the late X head contributes at most \(BA\) above the two
early-rank budgets, and the late Y head at most \(AB\). This is
exactly the hypothesis of the verified
\`WidthThree.WeightedPool.weightedComparisonCount_of_branchRankSum\`.
The weighted comparison-count inequality is impossible: the weighted
heads count more than \((A+B)\) times \(2/3\) of the total, whereas the
two low anchors sum to less than \(2/3\) of the total. Thus (1) suffices.

The argument needs no assumptions of independence of the order and
cut, and no product law. It is an exact finite counting implication.
The witness \(u_i\) (and \(v_j\)) need not be an actual label when it
is the sentinel. No subtraction with a negative result is used.

### Sharpness inside this two-envelope method

For given positive \(A,B\), write \(s=c+M\). If the only information
about the two head ranks is that one is at most \(C\) and the two
individual upper bounds are \(C+A,C+B\), then a nonzero integer
weight pair \((p,q)\) certifies both possible late-head cases at
anchor budget \(C+s\) precisely when
\[
                 pA\le(p+q)s,\qquad qB\le(p+q)s.
\]
The existence of such weights is equivalent to (1). Necessity:
multiply the first inequality by \(B\) and the second by \(A\),
add, then cancel the positive factor \(p+q\). Sufficiency takes
\((p,q)=(B,A)\). This is an exact obstruction to improving (1) by
merely changing these two weights. It is not an obstruction for
actual posets: a stronger argument can use the particular feasible
rank pairs, improved anchor ranks, or additional comparison data.

### Convenient simpler sufficient test

The two available finite bounds at a single pair can be specified
by local gate offsets \(d_i,e_j\): require \(x_i<y_{i+d_i}\) and
\(y_j<x_{j+e_j}\) when the corresponding endpoints exist. Then
\(u_i\le i+d_i\) and \(v_j\le j+e_j\) even at finite ends. If for each
incomparable pair either \(d_i\le c\) or \(e_j\le c\), it follows that
\(A\le c+M\) or \(B\le c+M\), respectively, which implies (1). The more
general local product test
\[
                  d_i e_j\le c(d_i+e_j)
\]
also suffices for that pair, by the transposed-weight proof of the
checked diagonal theorem applied just to those two offsets: its
two-high calculation does not require offsets on other labels.
One can mix these tests with (1) on different candidate pairs.

## Explicit switched ladder outside every fixed product cap

Take \(h=2\), and two rails of equal length \(n\) with
\(4\le m\le n-5\). Besides the individual rail orders, put in exactly
the following cross generators and take transitive closure:
\[
\begin{array}{ll}
x_i<y_{i+1}&0\le i<m,\\
x_m<y_{m+2},&\\
y_{m-2}<x_m,&\\
y_j<x_{j+1}&m\le j<n-1.
\end{array}
\]
All tail edges strictly increase the index, so the order is acyclic.
The following local cases cover every incomparable cross pair.

* If \(i<m\), the X offset is one. Thus \(A\le 1+i-j\le1+M\).
* If \(j\ge m\), the Y offset is one. For \(j=n-1\), this still gives
  \(v_j\le j+1=n\) by the sentinel. Thus \(B\le1+j-i\le1+M\).
* Otherwise \(i\ge m,j<m\). If \(i\ge m+1\) then
  \(y_j<y_m<x_{m+1}\le x_i\). If \(i=m,j\le m-2\) then
  \(y_j\le y_{m-2}<x_m\). The only remaining pair is \(i=m,j=m-1\).
  The two local offsets are at most two, since
  \(x_m<y_{m+2}\) and \(y_{m-1}<y_m<x_{m+1}\).
  More directly, \(B\le(m+1)-m=1\), so (1) holds.

For any **fixed** X offset \(d\) satisfying the earlier gate condition
it is necessary that \(d\ge n-m-1\): at \(x_{m+1}\) there is no path to
any Y label, since every such path needs a first X-to-Y edge and all
of those edges start at indices at most \(m\). For any fixed Y offset
\(e\) it is necessary that \(e\ge m\): the first Y-to-X edge on any path
from \(y_0\) has X-target index at least \(m\). Both lower bounds are
at least four, so \(de>d+e=(h-1)(d+e)\). Thus the earlier product-cap
theorem cannot cover this exclusive branch under the given labels.

In fact repartitioning into two rails cannot remove the obstruction.
The incomparability graph of the tail is bipartite with the two rails
as color classes, and connected. Each diagonal pair \(x_i,y_i\) is
incomparable because every edge strictly increases the index. Between
diagonal pairs with indices \(i,i+1\), the following incomparable edge
ensures connection:
- For \(i<m-1\), \(y_i\parallel x_{i+1}\), since there is no Y-to-X
  crossing ending at an index below \(m\), and the reverse direction
  decreases the index.
- For \(i=m-1\), \(y_{m-1}\parallel x_m\), since the sole Y-to-X
  crossing ending at \(m\) starts at \(y_{m-2}\).
- For \(i\ge m\), \(x_i\parallel y_{i+1}\): at \(m\) the first possible
  outgoing X crossing ends at \(m+2\); above \(m\) there is no outgoing
  X crossing at all. The reverse again decreases the index.

A connected bipartite graph has a unique bipartition up to swapping,
and any chain cover by two disjoint rails is a proper two-coloring
of its incomparability graph. The common ordinal chain prefix cannot
be made longer than two, since \(x_0,y_0\) are incomparable minimal
tail labels, or shorter than two in an attempt to improve the cap
(which requires \(h\ge2\)). Hence the fixed-offset failure persists
across all permissible rail labelings of this branch.

Adjoining one isolated \(a\) gives an actual width-three ambient
example: \(a,x_0,y_0\) are an antichain and the two rails plus \(a\)
supply a three-chain cover after extending one rail by the prefix.
The fixed-order insertion bijection gives
\(\Pr(a<b)=1/(|S|+1)=1/(2n+3)\). These examples distinguish the scope of
this local budget test from the earlier fixed-offset cap for this
exclusive branch and good pair. This does not assert that the ambient
examples are beyond other known classes (deleting \(a\) leaves width
two), or that another choice of good pair cannot prove balance.

## Formalization boundary

The previous Lean rank, single-target pooling, weighted-count and
first-high-assembly results have already been checked. This note's
new inputs are the two local rank bounds, comparable-head exclusion,
and switched-ladder specialization. No Lean, solver, or Git was run
for this note.
