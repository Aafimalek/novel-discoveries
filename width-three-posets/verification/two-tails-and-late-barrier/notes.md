# Two-tail obstruction and the one-vertex-off-chain case

Assume the good-pair hypotheses: a,b are incomparable, every strict predecessor
of a precedes b in the poset, and S is b together with the successors of b
that are not successors of a. Put p=P(a<b). Suppose S minus b is partitioned
into two nonempty chains C=x_1<…<x_r and D=y_1<…<y_s. Additional relations
between these chains are allowed. Throughout, a comparison within a probability
is a comparison in a uniformly random linear extension of the finite poset.
A balanced pair is a pair of distinct elements whose earlier-order probability
lies in [1/3,2/3]. In width three, every member of S is incomparable with a,
so S has width at most two, and the two-chain partition is available when
S minus b is not a chain. Suppose p≤1/2 and there is no balanced pair.

Write F(z)=P(a<z), and call z low if F(z)<1/3 and high if F(z)>2/3.
All branch vertices have one of these statuses. Since p≤1/2 and a,b are
not balanced, F(b)=p<1/3, so b is low. Along each chain the low vertices
form an initial segment. Let their lengths be i,j.
Then necessarily

    r-i > min(i,j),   s-j > min(i,j),   i<s,   j<r.                 (1)

In particular, the last vertex of **each** chain must be high. These
constraints apply to every partition into two chains, not just one chosen
to maximize an initial segment.

Proof. Fix the induced branch order. For a positive cut k, swap a with
the kth branch vertex z, the last member of S before a. Moving a earlier
crosses no predecessor of a: each such predecessor is strictly below b≤z.
Moving z later crosses no successor of z: if h lay strictly between z and
a and were a successor of z, then b<h, and a<h would contradict the
original extension. Thus h would be in S, contradicting that z was the last
member of S before a. The pair a,z is incomparable. No branch vertex
lies strictly between them, so the branch order is unchanged and the cut
falls by one. In the image, z is the first member of S after a, so the swap
is uniquely inverted. This proves antitonicity within each fixed order.
Summing over branch orders gives antitonicity of the unconditional bin
probabilities; in particular the final bin is no larger than the initial
bin, whose probability is p.

Let ρ_R(z) be the one-based position of z in the branch order of an
extension R. The cumulative sums in a fixed order are subadditive, by
termwise comparison of a shifted interval of bins to the interval of
the same length starting at zero. Hence if
ρ_R(v)≤ρ_R(u)+ρ_R(w) in every extension, then F(v)≤F(u)+F(w), by averaging.
The inference allows u=w.

If C has a first high vertex x_(i+1), its position is at most i+s+2,
since later vertices of C cannot precede it. Let u=x_i or b for i=0;
define w=y_j or b the same way. The earlier anchor has position
at least 1+min(i,j); the later has position at least 1+i+j because
both initial segments are present by then. Thus if s-j≤min(i,j), the
pooled position bound forces F(x_(i+1))≤F(u)+F(w)<2/3, a contradiction.
Similarly, existence of a first high on D implies r-i>min(i,j).
If both ends are low, then by the two-end cover and the final cut bound,
1≤F(x_r)+F(y_s)+P(all S before a)≤F(x_r)+F(y_s)+p<1, a contradiction.
If just one end is low, its entire chain is low, and the first-high
bound on the other chain gives a contradiction. Hence both ends are high
and the two tail inequalities hold. Finally ρ_R(u)≥i+1, so i≥s would
give ρ_R(x_(i+1))≤i+s+2≤2ρ_R(u), again a contradiction by pooling u
with itself. Swap the arms for j<r.

## Infinite sufficient class

If S minus b is a nonempty chain x_1<…<x_r and at most one further
vertex y, a balanced pair is guaranteed whenever

    p ≤ 1/6 + 1/[3(max(1,d)+2)],

where d is the number of long-chain vertices that are not strict
successors of y. (When there is no y, the standard chain proof applies
at p≤1/2.) In particular d≤r gives the simpler threshold
1/6+1/[3(r+2)]. If y is comparable with x_1, a balanced pair is
guaranteed at p≤1/2 independently of r. If y<x_2 and y is incomparable
with x_1, the bound is 5/18 independently of r.

Proof. Under no balance, take s=1 in (1), obtaining i=j=0: every
nonroot branch vertex is high. The >2/3 preferences on the branch
vertices form a strict total order: a directed triangle would have
positive probability of all three edges by the union bound, which
no linear order can realize. Thus the first nonroot vertex e in this
majority order is x_1 or y and strongly precedes every point of the
opposite arm. If e=x_1 use the opposite list of length m=1. If e=y
use only the first d points of the opposite chain, so m=d, because
the other points cannot precede y in any extension. If y and x_1 are
comparable, the smaller is second in every branch order, so its
F value is exactly q_0+q_1≤2p<2/3, contradicting that it is high.
This proves the p≤1/2 alternative before using the harmonic bound.

Fix an induced branch order and decompose its decreasing cut
probabilities into nonnegative weights on uniform prefix-cut
components: weight at cutoff k is the difference of bin k and bin
k+1. In a component with h cuts (cuts 0 through h-1), write t for
the number of opposite-list vertices before e, so e has rank t+2.
For the opposite list z_1…z_m the expression

    P(b<a) + P(a<e)/2 + sum_{j=1}^m P(e<z_j)/[(j+1)(j+2)]

has component value

    1 - 1/h + min(1,(t+2)/h)/2 + 1/(t+2) - 1/(m+2).

The telescoping sum gives the last two terms. This is at most
3/2-1/(m+2): for h≤t+2 compare 1/h to 1/(t+2); for h≥t+2 replace
(t/2)/h by its upper bound (t/2)/(t+2). Averaging preserves the
bound. But P(b<a)=1-p and the other listed comparisons are strictly
greater than 2/3. Their coefficients have sum 1/2+(1/2-1/(m+2)).
Substitution gives p>1/6+1/[3(m+2)], contradicting the stated cap
because m≤max(1,d). This is a written proof; its inequalities are
not fully formalized here, and no novelty claim is made.

## Late three-by-four branch obstruction

The four positive cutoff components are:

| branch order | last allowed cut | per-cut weight |
|---|---:|---:|
| b x1 x2 x3 y1 y2 y3 y4 | 3 | 2 |
| b x1 x2 x3 y1 y2 y3 y4 | 5 | 2 |
| b x1 x2 x3 y1 y2 y3 y4 | 8 | 1 |
| b x1 y1 y2 y3 y4 x2 x3 | 6 | 2 |

Here cuts insert a after the listed number of branch labels.
This is an antitone histogram with total 43 and p=7/43<1/6. Its
majority order is b,x1,a,x2,x3,y1,y2,y3,y4; every forward count is at
least 29 of 43, so no pair is balanced. Therefore the earlier tactic
"eliminate late majority orders, then use the harmonic early bound"
cannot carry through using antitonicity alone on arbitrary arms.
This distribution is not realizable by uniform linear extensions of any poset:
conditioning a uniform linear extension on b<a, when that event is nonempty,
gives the uniform linear extension law of the poset with b<a added and closed
transitively. In the conditioned law, Shepp’s XYZ inequality on x2<a and
y2<a would require 14·9≤36·3,
which fails. Nevertheless all unconditional XYZ correlations hold
(by separate exact arithmetic enumeration), so marginal XYZ is not
enough to exclude this particular pattern.

## References and dependencies

- The branch-order-preserving bin injection and the pooled-rank implication are
  previous ingredients of this project. The short pooled-rank argument above
  derives the latter from the former directly.
- L. A. Shepp, [The XYZ Conjecture and the FKG Inequality](https://doi.org/10.1214/aop/1176993791),
  *Annals of Probability* 10 (1982), 824–827. Its same-sided correlation
  also applies with all order directions reversed by passing to the dual poset.
