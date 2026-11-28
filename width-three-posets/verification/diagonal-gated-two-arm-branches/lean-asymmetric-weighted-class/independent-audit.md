# Independent proof audit: asymmetric (weighted) diagonal gates

Let the exclusive branch, good pair, labeling, and cap
\(\Pr(a<b)\le 1/2\) be exactly those of the checked rank-only diagonal
theorem. Common prefix length is \(h\ge2\); the increasing rails are
indexed from zero. Allow any extra acyclic cross relations. Suppose the
finite diagonal gates \(x_k<y_{k+d}\), \(y_k<x_{k+e}\) hold whenever the
respective endpoints exist. The cap for this proposed extension is
\[
de\le(h-1)(d+e).
\]
This document audits the written mathematics independently. The
accompanying Lean sources and fresh typed endpoint audit were checked
separately under the strict pinned replay documented in README.md.

## Weighted count implication

For every induced branch order the checked swap keeps its ambient
cut-count sequence \(c_k\) antitone. If the branch has \(m\) points,
these counts are for \(0\le k\le m\); use \(c_{m+1}=0\), not a nonexistent
count at a new legal cut. For \(1\le T\le m+1\) put
\(w_T=c_{T-1}-c_T\ge0\). For any legal one-based branch rank \(r\),
\[
\sum_{k<r}c_k=\sum_{T=1}^{m+1} w_T\min(r,T).
\]
This is finite telescoping: \(c_k=\sum_{T>k}w_T\). In particular the
last legal cut contributes to the leading counts through differences,
but contributes directly to no \(\{k<r\}\) event when \(r\le m\).

If \(p,q\) are nonnegative weights and
\(pr_x+qr_y\le(p+q)(r_u+r_v)\), the capped weighted left hand at any \(T\)
is at most both \((p+q)T\) and \((p+q)(r_u+r_v)\).
Moreover \(\min(r_u+r_v,T)\le\min(r_u,T)+\min(r_v,T)\):
one anchor at or above \(T\) alone suffices, otherwise the sum of the
individual caps is \(r_u+r_v\). Thus each capped difference is
nonnegative; multiply by \(w_T\), sum, then sum the comparison-count
inequality over fibers. Implementing the fibers by the four rank
coordinates rather than by full induced orders is valid: these
coordinates are invariant under the swap, so the same monotone-cut
argument applies. This is not a factorization or an equal weighting
of induced branch orders. The implication works with either weight
zero, both weights zero, and equal anchors.

## Two highs and the transposed weight orientation

The already checked all-low, one-high and common-prefix cases are
unchanged. Given both first highs \(x_i,y_j\), choose the prior fixed
low anchors. For every ranking their rank sum satisfies
\(A\ge 2h+i+j+M\), with \(M=\max(\min(i,j),|i-j|)\).
Put \(B=h+i+j+1\). Both bounds below are unconditional on the heads
being comparable or incomparable:

* One head rank is at most \(B\): only the two initial rail prefixes and
  the common chain can precede the earlier head.
* The finite X-direction gate gives
  \(r_x\le h+i+(i+d)+1\le B+d+M\).
  Indeed, an opposing label before \(x_i\) cannot have index at least
  \(i+d\); the existence of such a label would force the gate endpoint
  to exist, and the gate followed by the Y chain would forbid its early
  position. If the finite gate endpoint does not exist, all opposing
  indices are already below \(i+d\). The Y bound is
  \(r_y\le B+e+M\).

Use the **transposed** coefficients \(e\) for X and \(d\) for Y.
The extra weighted rank above \((d+e)B\) is at most \(e(d+M)\) if X
is late, or \(d(e+M)\) if Y is late. Both are bounded by
\(de+(d+e)M\le(d+e)(h-1+M)\). Since
\(A\ge B+(h-1)+M\), weighted comparison-count pooling applies. The lack
of a strict comparison between the heads does not enter this proof.

For total ranking count \(N\), both anchors have strict comparison
counts below \(N/3\); both heads have strict comparison counts above
\(2N/3\). Multiply the strict anchor sum by the positive weight
\(d+e\) and use the head inequalities in their non-strict form. This
contradicts the weighted pooling inequality even if one coefficient
vanishes. If \(d=e=0\) and both heads exist, the two rails are nonempty
and the two index-zero gates contradict strict order directly. Empty
rails are handled by the unchanged all-low or one-high cases.

## Scope checks

The checked simpler cap implies the product cap: if \(d,e\le2(h-1)\)
then \(de\le2(h-1)d\) and \(de\le2(h-1)e\); add and cancel two.
If either offset is at most \(h-1\), the other is unrestricted by the
product cap. At \(h=4,d=4,e=12\) both sides of the cap are 48; the
maximum offset 12 exceeds the prior rank-only bound 6 and the prior
written conditional-XYZ bound 7.

For equal tail lengths at least 16 and only the specified gates,
comparability from X to Y requires gap at least four and from Y to X
at least twelve, by the first cross edge of each directed path; the
bound is attained by taking that gate and then the target rail.
Thus the maximum opposite-rail incomparability degree is 15, attained
already with 16 labels on each rail. Adjoining an isolated distinguished
\(a\) realizes width three and the good-pair cap; in each fixed branch
order exactly one of \(|S|+1\) insertion slots for \(a\) is before \(b\).
This example distinguishes the two specific older offset caps from
the new one; it is not a literature-wide novelty or difficulty claim.

The argument proves neither the unrestricted width-three conjecture
nor any conditional XYZ statement. The bounded exact script is a
diagnostic, not the proof and not a Lean receipt.
