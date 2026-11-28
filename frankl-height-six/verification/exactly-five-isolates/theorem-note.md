# Five isolates force block-degree deficit at most two

**Written theorem with a finite integer replay. Not yet checked end to
end in Lean.** Let a weak minimum-ground counterexample at height at most
six have exactly five isolated points and at least two forcing-star
centers. Its omitted-star pair design has maximum block-degree deficit at
most two. No unary-star hypothesis is needed for this theorem. An
additional argument below bounds the number of deficit-two centers
without an extra hypothesis. General cases with deficits zero, one, and two, and
the single-source branch, are not excluded.

## Setup

Let k count sources, Q = binom(k,2), N count omitted-star blocks, and
g_v count blocks through v. Write d_v = k−1−g_v and d = max d_v.
Choose a minimum-degree center p, with g = g_p = k−1−d. At any
center v the other points of its blocks partition the other k−1
centers, so

    d_v = sum over B containing v of (|B|−2),   1 ≤ g_v ≤ k−1.

Let H(m) = 1+m+binom(m,2). For distinct anchors p,q and anchor
block B, omit all of B. The exterior blocks through p give g−1
groups of equal occurrence signature. The sharp compressed
Sauer bound on the pair-avoidance fiber is H(g+4): the g−1
groups plus five isolates. The fiber's lower bound is

    |F(p,q)| ≥ n+k+N−g_p−g_q ≥ N+k+7+d+d_q.       (1)

Here n≥2k+5, and exactly N−g_p−g_q+1 blocks avoid the anchor pair.
If q's exterior groups merge r independent pairs of the p groups,
the upper bound lowers to H(g+4−r).

For any block of size r≥2 its loss of blocks from the all-pair
design is binom(r,2)−1 ≤ 2r(r−2)/3. Thus

    Q−N ≤ (2/3) sum_v d_v ≤ 2kd/3.                (2)

We also use the preceding incidence Cauchy bound
N ≥ k g²/(k−1+g).

## 1. Remove deficits at least six and restrict all others

Drop d_q in (1). Comparing the starting bounds, substituting
the Cauchy bound, and clearing the positive denominator yields

    (d−12)g²+(d−12)g+d(4d−6) ≤ 0.

For d≥12 the left side is positive, so d≤11. Substituting (2)
instead shows that the slack between the upper and lower
bounds is at most

    Δ = (3−d/3)k + (d²−9d)/2.                     (3)

The first extra merger costs g+4 = k+3−d. For d≥6,
the difference Δ−(k+3−d) is nonincreasing in k and at k=d+2
equals (d²−13d+6)/6, negative for 6≤d≤11. Therefore no extra
merger is possible under those deficits.

For d=3,4,5, two extra independent mergers would cost
2(k+3−d)−1 > Δ. Thus only one extra merger is possible.
In either reasoning, take any block C not through p and
any q∈C. Its other points are outside B, since distinct
blocks share at most one point. They lie in distinct p
groups, since otherwise C and a block through p would
share at least two points. Consequently C forces |C|−2
mergers. For d≥6, all nonpair blocks must pass through p;
for d=3,4,5, all blocks outside p have size two or three.

When all nonpair blocks pass through p, their positive
excesses e=|B|−2 sum to d. The lost-block count
Q−N = sum (e²+3e)/2 is at most (d²+3d)/2.
With this bound instead of (2), (3) improves to slack at
most (d−3)(d−k). This excludes every d>3; for d=3 the
slack is at most zero, and choosing q in any nonpair block
through p supplies its d_q≥1, also impossible. We are left
with d=3,4,5 and at least one off-p triple.

## 2. Group charging bounds the number of centers

The nontrivial groups through p have sizes t_i=e_i+1, where
the positive e_i partition d. Let m=sum_i t_i. The other
k−1−m groups are singletons. For any q in a singleton group,
if it lies on s≥2 off-p triples, their pairs of other
vertices must all join the same two p groups. Otherwise
two distinct links between group labels give two independent
mergers. The s pairs are vertex-disjoint because two
distinct triples sharing q cannot share a second point.
In particular the two partner groups are nontrivial and
s≤min(t_i,t_j). Each pair can be used by at most one q,
by pair uniqueness.

Give each singleton q baseline deficit one, then charge s−1
when s≥2. For a fixed pair of nontrivial groups, the sum of
these charges over assigned singleton vertices is at most

    (1−1/min(t_i,t_j)) t_i t_j = t_i t_j−max(t_i,t_j).

Every vertex in the m nontrivial groups, and p itself, has
deficit at most d. Hence

    sum_v d_v ≤ k + C,
    C = (d−1)(1+m) + sum_{i<j}(t_i t_j−max(t_i,t_j)).

The maxima over partitions of d=3,4,5 are 20,39,64. This
tiny computation is checked in the replay. Substituting
this refined deficit bound into (2), the slack in the
starting comparison improves to

    (3−d+2/3) k + (d²−9d)/2 + 2C/3.

Now anchor at any q in an off-p triple. This costs one
extra merger k+3−d and at least one from d_q in (1).
For d=3,4,5 the resulting inequalities give k≤10,12,14
respectively.

## 3. Exact partition check eliminates all those cases

For a fixed partition of d and a fixed k, include all
singleton p groups by setting their e_i=0. As noted above,
each off-p triple takes one vertex from each of three
distinct p groups. For any q in group i, even a nonsingleton
group, all its off-p triples must use the same two partner
groups: the anchor block for p,q drops group i, and two
distinct links on the other labels would force two independent
mergers. The number of its off-p triples cannot exceed d−e_i
or the second-largest size among the other groups. The latter
is because the two selected partner groups must each supply
a different vertex per triple. Therefore for t off-p triples,

    3t ≤ sum_i (e_i+1) min(d−e_i, second_largest_other_size_i).

With fewer than three groups there cannot be an off-p triple.
The exact loss is

    Q−N = sum_i (binom(e_i+2,2)−1) + 2t.

In contrast, using the tightened anchor upper H(g+3) in (1)
with d_q≥1 requires

    Q−N ≥ (d−2)k+(6+7d−d²)/2+1.

The self-contained standard-Python replay considers every
positive partition of d, every k from d+2 through its proved
bound, and all forced singleton groups. There are 12,24,39
eligible rows with at least three groups for d=3,4,5.
The largest values of the maximum allowable loss minus the
necessary loss are −2, −9, −12, respectively. No row survives.
This completes the maximum-deficit-two conclusion.

## Optional sharpening in the deficit-two branch

Assume now d=2. Let D count the
deficit-two centers and M=Q−N. Only triples and four-blocks
can be nonpairs, and the latter do not meet any other nonpair
block since all their vertices are already at deficit two.
Equation (2) gives M≤2(k+D)/3≤4k/3.

For any fixed deficit-two center r, at most four other
deficit-two centers share a nonpair block with r. For any
other deficit-two center q the anchor block is an ordinary
pair. Their four exterior identification units are independent
except in the alternating four-cycle of two mate-pairs on
each side, as in the four-isolate theorem. For fixed r there
is at most one such cycle partner q: in the dual simple
graph on triples, where a degree-two center is an edge,
the two endpoints of r's edge have at most two common
neighbors (the dual maximum degree is three). The cycle
partner would have to be the edge between those two neighbors.
No such cycle is possible for r belonging to a four-block.
Call a pair with all four independent units a good pair.

If any good pair exists, its fiber projects onto at most
k−1 coordinates (k−2 outside centers, five isolates, and
four identifications). By (1), M≥k+10 is necessary, so
D≥k/2+15 by the bound on M. Also k≥30 follows from
k+10≤M≤4k/3. This forces all stars to be unary in the
good-pair case: the checked multileaf bound with a second
source would give n+k≤2+5+binom(5,2)=17. Consequently every
deficit-two center has at least two good partners. For every good pair
the slack at H(k−1)=Q+1 is M−k−10≤k/3−10, smaller than
k−2. The preceding rank-two atom bound now forces exactly
k−1 supported quotient coordinates with all singleton
omissions. In particular each isolate can be omitted from
the full pair maximum on its own. Taking two good partners
for a center r and unioning the relative omission sets
yields a ground complement consisting of r's whole star
and any specified isolate. For one good anchor pair the
remaining D−2 deficit-two stars therefore give 5(D−2)
extra mixed omission witnesses, distinct from top,
single-point avoidance maxima, source witnesses and pair
maxima by the same argument as in the four-isolate proof.
This number exceeds the slack M−k−10, contradiction.

Thus there is no good pair. If D≥7, the at-most-five
exceptions for a fixed r would give a good pair, so D≤6.
This also shows that M≥k+10 is impossible: that inequality
alone forces D≥k/2+15 and hence a good pair. The low-loss
branch with D≤6 is not ruled out.

## Verification map

Run python3 deficit_replay.py. The formal prerequisites
are the verified pair design and omitted-block identification
(starBlocks_pairDesign, block_eq_omitted_for_member_pair),
link signatures (compressed_pair_signatures_eq_of_blockLink),
compressed Sauer (pair_fiber_card_le_sauer_block_signatures),
and witness count (leaf_pair_count_with_blocks). The optional unary
reduction invokes multileaf_center_isolated_bound_with_sources. The starting
Cauchy bound is the incidence proof used in the checked
FranklAtLeastThreeIsolates module. The optional last section
reuses the handwritten four-isolate rank-two atom refinement
and mixed witness argument, not a new Lean claim.
