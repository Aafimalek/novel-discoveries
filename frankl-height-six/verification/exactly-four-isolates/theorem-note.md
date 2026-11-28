# Exactly four isolates: all multiple-source counterexamples excluded

**Written argument (not checked end to end in Lean).** Under the same weak
frequency, minimum-ground, and height-six hypotheses as the four-isolates
bound, a family with exactly four isolates must have exactly one forcing
source. A separate finite trace calculation below reduces that remaining
case to one explicit trace family, but does not rule it out.

Throughout, `k` counts sources, `N` counts blocks of the omitted-star
pair design, `Q=binom(k,2)`, and `H(m)=1+m+binom(m,2)`. A block of
size `r` incurs lost-block count `binom(r,2)-1` from the all-pair
design. Write `d_v=k-1-g_v` for the deficit of vertex `v`.
Pair uniqueness implies
```
 d_v = sum_{B contains v} (|B|-2).
```
If a pair-avoidance fiber is supported, after forced identifications,
on at most `m` coordinates, then its cardinality is at most `H(m)`.
Its existing witness lower bound (using ground size at least `2k+4`)
for anchors `p,q` is
```
 |F(p,q)| >= N+k+6+d_p+d_q.                           (A)
```
This is `n+k+(N-g_p-g_q+1)-1` with `n>=2k+4`.

Zero sources give a four-point ground and are impossible by the
external 12-point theorem, as are all ground sizes at most twelve:
adjoin the empty set to convert a no-strict-majority family into an
ordinary below-half counterexample. If there are two or more sources
and a nonunary star, the earlier multileaf lemma gives `n+k<=12`
at four isolates, again impossible. Hence in the rest of the
multiple-source proof all stars are unary, `n=2k+4`, and `k>=5`.

## 1. Maximum degree deficit at most two

Choose a minimum degree `g` at `p`, put `d=k-1-g`, and anchor
with any distinct `q`. The checked block link groups from `p`
give `|F(p,q)|<=H(g+3)`. From (A) the lower bound is at least
`N+2k+5-g`. Substitute the earlier incidence bound
`N>=k*g^2/(k-1+g)`. Clearing the positive denominator yields
```
 (d-8)g^2+3dg+4d^2 <= 0.
```
Since `g>=1`, this implies `d<=7`. The block contribution
`binom(r,2)-1 <= 2r(r-2)/3` and `sum_v d_v<=kd` give
`N>=Q-2kd/3`. Substituting this instead bounds the available
slack between the upper and lower bounds by
```
 (2-d/3)k+(d^2-7d-4)/2.
```
This is negative at `d=6,7`. For `3<=d<=5`, even one
merger of the available anchor groups costs `H(g+3)-H(g+2)=g+3`,
which exceeds that slack: the differences for `d=3,4,5`
are respectively `7`, `k/3+6`, and `2k/3+4`.
Thus every exterior group through `q` is contained in an
exterior group through `p`. Pair uniqueness makes every nonpair
block incident to `p`, exactly as in the three-isolate argument.
For clarity: if a non-anchor block through `q` had two exterior
points, they would also belong to one different block through
`p`, repeating their pair. The conclusion holds for arbitrary
`q != p`.

With all nonpair blocks through `p`, their positive contributions
`e=|B|-2` sum to `d`. Their lost-block count is
`(e^2+3e)/2`; convexity (or `sum e^2<=d^2`) gives
`N>=Q-(d^2+3d)/2`. The available slack is then at most
`(d-2)(d-k)-2<0` for `3<=d<=5`. Therefore `d<=2`.

## 2. A reusable near-extremal counting observation

After identifying the forced equal coordinates in a pair fiber,
complement its members relative to its true support. This
gives an intersection-closed family with the empty set and no
four-member strict chain. The rank-two atom bound proved in the
preceding note gives, on at most `m` coordinates, at most
`1+m+binom(a,2)` members, where `a` is the number of disjoint
nonempty atoms. Thus if the deficit from `H(m)` is less than
`m-1`, all `m` atoms are singletons. In particular all coordinates
are genuinely available, the fiber maximum is full support, and all
relative singleton omissions belong to the complemented fiber.
If only `a>=m-1` is known and the true support is all `m`
coordinates, all but at most two coordinates are singleton atoms;
if two fail to be singleton atoms they form a two-coordinate atom.
If one available coordinate is absent from the support, the true
support has exactly `m-1` coordinates and all its atoms are singletons.

Call a ground complement `S_r∪J` a mixed omission if it is the
complement of some family member, where `S_r` is a unary star
and `J` is a nonempty isolate subset. When `r` is outside the
anchor pair, this counts as an extra witness in (A): the member
contains both anchor leaves, but is distinct from the ground,
single-point avoidance maxima (at least three original points are
omitted), source witness maxima (omits a leaf), and pair maxima
(omits only one whole star). If two different pair blocks
`{r,a}` and `{r,b}` have full available support and both possess
the *same* relative isolate omission `J`, unioning those two
members gives the mixed omission `S_r∪J`.

## 3. Deficit zero: all-pair design

Here every anchor pair has `m=k+2` available coordinates before
optional identifications. Its bound from below is `Q+k+6`, while
`H(k+2)=Q+3k+4`, leaving slack `2k-2`. If `a<=k`, the
atom bound gives at most `1+(k+2)+Q=Q+k+3`, impossible.
Thus every pair has at least `m-1` atoms and at least two of
the four isolates are singleton atoms.


For each source `r`, consider the `k-1` anchor pairs through `r`.
For a fixed such pair the exact original isolate omissions, in
members omitting just those two stars, include one of the following
three lists:

1. At least three singleton isolates (full support).
2. Exactly two singleton isolates and their complementary two-isolate
   set, which is the two-coordinate atom (full support).
3. Some singleton `{z}` and all pairs `{z,w}` with `w!=z`:
   this is the case of a missing coordinate. It must be an isolate
   `z`, since the maximum omits exactly the anchor stars. All other
   coordinates are singleton atoms on the true support, giving the
   displayed omissions by deleting those coordinates or none.

The union of two such members with different anchor partners has
complement the star `S_r` together with the intersection of their
isolate omissions. We claim at least three distinct nonempty
intersections for each `r`.

- If two lists are of type 3 with the same missing isolate, their
  common list already gives four. With different missing isolates
  `z,w`, the cross-intersections give `{z},{w},{z,w}`.
- If exactly one list is of type 3, every singleton isolate omission
  of another list can be intersected with a type 3 omission to
  obtain that singleton. If only two singletons occur in all other
  lists, all those lists have type 2 with a common complementary
  pair `J`. Intersect `J` with a suitable type 3 omission to
  obtain any one singleton in `J`.
- If none is of type 3, at least two isolates appear as singletons in
  at least two lists apiece: otherwise there are at most
  `(k-1)+3 < 2(k-1)` singleton occurrences. If three or more are
  repeated, their singleton intersections suffice. If only two
  are repeated, the other two appear a combined total at most
  twice. At least `k-3>=2` lists are then type 2 with the same
  complementary pair of these two non-repeated isolates. This
  yields the third nonempty intersection.

Therefore at least three mixed omissions are available for each
outside star. For any fixed anchor pair the resulting
`3(k-2)>2k-2` extra witnesses exceed its slack, a contradiction.

## 4. Deficit one: disjoint triples

If the maximum deficit is one, the only nonpair blocks are vertex-
disjoint triples. Let there be `t>=1`, so `N=Q-2t`.
For anchors in two distinct triples the anchor block is a pair,
and the two disjoint mate pairs each collapse to one coordinate.
Thus `m=k`. Their lower bound is `Q-2t+k+8`, so the slack
in `H(k)=Q+k+1` is `2t-7`. This is negative for `t=2,3`;
when `t>=4` it is less than `k-1`, since `3t<=k`.
Thus all quotient singleton omissions exist and the maximum
has full support on the quotient. For any vertex in a triple
and any isolate, taking two partners from another triple gives
the mixed omission of its star and that isolate. This provides
`4(3t-2)>2t-7` extra witnesses for a fixed distinct-triple
anchor pair, impossible.

If `t=1`, use an anchor consisting of a vertex of that triple and
one outside it. The anchor block is a pair and the only required
identification is one mate pair, so `m=k+1`. The lower bound is
`Q+k+5`; slack `k-3` is less than `m-1`. Again all quotient
singletons exist. Every source can take two partners from the
opposite side of the partition into triple and outside (the
outside has at least two vertices because `k>=5`). It follows
that every source gives all four mixed singleton isolate omissions.
The resulting `4(k-2)>k-3` witnesses exceed the slack.

## 5. Deficit two: triples and four-blocks

Now each four-block is disjoint from all other nonpair blocks:
each of its vertices is already at deficit two. A vertex outside
the four-blocks belongs to at most two triples. If there are
`t` triples and `u` four-blocks, put
`S=Q-N=2t+5u`. Counting total deficits gives
`3t+8u<=2k`, hence `S<=4k/3`.

Two distinct deficit-two anchors have lower bound `Q-S+k+10`,
which is greater than `H(k-2)=Q-k+2`. Thus any geometry
compressing their fiber to at most `k-2` coordinates is impossible.

For such anchors in different blocks (their anchor block is a
pair), start with `k+2` available coordinates. Each anchor
contributes two units of identification among outsider stars:
either one three-point group (for a four-block), or two disjoint
two-point groups (for two triples). Groups from opposite anchors
meet in at most one point, by pair uniqueness. The four units
of identification are independent unless both anchors consist
of two mate pairs and the four pairs make a cycle of length four.
To see this, form a bipartite graph with the two anchors' groups
as vertices and an edge for each star in both groups. Groups
on each side are disjoint, and the graph is simple by pair
uniqueness. The number of identifications contributed independently
is four minus its cycle rank: adding an identification within a
group joins two coordinate classes unless they were already
joined via a sequence of groups on the opposite side. Equivalently,
in each connected component with `v` groups and `e` pairwise
overlaps, the number of distinct covered coordinates is
`sum(group sizes)-e`; the forced reduction there is that number
minus one, less than the sum of the group reductions by
`e-v+1`. With at most two groups on each side the only possible
cycle is the four-cycle, and it requires both sides to have two
groups. Without it there are four identifications, which is
impossible by the preceding cardinality observation.

### A four-block exists

No deficit-two vertex can lie outside the four-block, since the
preceding argument would require its three-point group to be on
a four-cycle. Thus there is one four-block, and all other
nonpair blocks are disjoint triples. If any triple exists, take
one anchor in the four-block and one in the triple. Their group
reductions are independent and total three, so `m<=k-1`.
But `S=5+2t<=5+2(k-4)/3<k+8`, and (A) gives
`Q-S+k+9>Q+1=H(k-1)`, impossible.
If no triple exists, two anchors inside the four-block have
`m=k` and (A) gives `Q-5+k+10>H(k)`, also impossible.

### Only triples, with at least one deficit-two source

Make a simple graph with one vertex for each triple and one
edge for each source belonging to two triples, joining those two
triples. It has maximum degree three, since a triple has three
sources. Any two disjoint edges correspond to separate deficit-
two anchors whose mate pairs must form the above four-cycle.
Each of the four intersections gives a source incident with
one triple from each edge, hence the four cross-edges of a
literal `K4`. Its four vertices are cubic within the `K4`,
so any further edge would be disjoint from it. Such an edge,
together with an edge from the `K4`, would require cross-edges,
which is impossible. If there are no disjoint edges, the family
of edges is pairwise intersecting; in a simple graph this is
a star or a triangle. With maximum degree three it has at most
three edges. In either case the number `D` of deficit-two
sources is at most six.

If there are at least two deficit-two sources, take any two.
If they belong to a common triple, that block removes three
stars, leaving `k+1` available coordinates; their two different
outer mate pairs give two independent identifications. If they
do not, their mates give the four-cycle and three independent
identifications on `k+2` coordinates. Thus `m<=k-1` in
both cases. From (A), `S>=k+9` is necessary, but
`3t<=k+D<=k+6` gives `S=2t<=2(k+6)/3<k+9`,
a contradiction.

Finally suppose there is exactly one deficit-two source `p`.
If a triple other than its two exists, it is disjoint from
both; a source `q` of that triple has deficit one. Their
three independent group identifications give `m<=k-1`;
(A) would require `S>=k+8`, whereas `3t<=k+1` implies
`S=2t<=2(k+1)/3`. If the only triples are the two through
`p`, choose a mate of `p` in one triple as the other
anchor. Removing the anchor triple leaves `k+1` coordinates,
and the other mate pair collapses once, so `m=k`. But (A)
gives `Q-4+k+9>H(k)`.

All three possible maximum deficits are excluded, completing the
multiple-source claim.

## 6. Remaining one-source trace family: an exact finite reduction

Let `I` be the four isolates and `L` count the leaves at the
unique source. Let `P` be the family of traces on `I` of the
source-containing members, and let `B` be the source-avoiding
family. Every source-containing set contains the entire star;
the checked top and co-singleton facts put all 3- and 4-subsets
of `I` in `P`. The checked smaller-ground reduction gives
an isolate `x` of strictly below-half frequency in `P`;
rename it coordinate zero. The trace of any member of `B`
must be one of the safe traces `T`, defined by
`T∪R in P` for every `R∈P`.

The self-contained exact replay `traces.py` exhausts the
`2^11` choices for the optional traces, rejecting families
not union-closed or without the requisite low point. There
are 106 remaining labeled families. For each candidate and
each pair of isolates `y,z`, it computes
```
 s = |union of all safe traces avoiding y,z|;
 a = frequency_P(y)+frequency_P(z)-|P|.
```
If `a>s` and the safe supporting union is contained in the
bottom trace of a four-member chain in `P`, the candidate
is impossible. Indeed the source-avoiding family omitting
both `y,z` can extend any chain by those four
source-containing members, and thus has height at most two
on at most `L+s` points. Its cardinality is at most
`L+s+1`. Meanwhile there are at least `L+1` source-
avoiding members containing both isolates (the full source-
avoiding top and its co-leaf tops). Inclusion–exclusion
and the two weak-half bounds give at least `L+1+a`
members omitting both, a contradiction.

The replay excludes 105 and leaves exactly the trace family
`P=2^I \ {{x}}`. Its four frequencies are `7,8,8,8`
out of 15. This model is not excluded by the calculation:
no claimed contradiction for the exactly-four-isolate,
one-source case.

For this residual, write `b=|B|`. The high isolates each
occur at most `(b-1)/2` times in `B`, and the low isolate
`x` is the only possible strict majority in `B` by smaller
ground minimality (every leaf occurs in all 15 source-containing
sets). The full-family bound then gives `b` odd with
`f_B(x)=(b+1)/2`. Trace `{x}` is forbidden. The empty-trace
subfamily of `B` has at most one member: a two-chain would
follow with five source-containing sets whose isolate traces
form a maximal chain beginning at the empty trace.
Let `b_j` count members of `B` containing exactly `j` of the
three high isolates. The sum of their frequencies gives
`b_1+2b_2+3b_3 <= 3(b-1)/2`, which rearranges to
`b_1>=b_2+3b_3+3-3b_0>=3(L+1)`, as `b_0<=1` and the full
source-avoiding top and the `L` co-leaf tops contribute to
`b_3`. These constraints do not complete the remaining case.

## Verification and dependencies

Run `python3 traces.py` for the finite trace check. The new
multiple-source proof is handwritten. It uses the same checked
`starBlocks_pairDesign`, link-closure, compressed Sauer and
extra witness modules as the at-least-four result, along with
`multileaf_center_isolated_bound_with_sources`; the atom bound
is the written lemma from the three-isolate proof. The one-
source trace reduction uses `exists_low_frequency_in_containing_fiber`,
`unique_source_all_nonisolates_present`, `isolated_coSingleton_mem`
and `card_le_top_card_add_one`.

Small ground sizes in the multiple-source proof use
[Vučković and Živković, *The 12-Element Case of Frankl's
Conjecture*](https://ipsitransactions.org/journals/papers/tir/2017jan/fullPaper.pdf).
