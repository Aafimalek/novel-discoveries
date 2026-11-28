# Equality can be prescribed with up to six off-grid additions

This is a written lemma for the pinned G449: let x be an original
vertex and z a new off-grid point not at unit distance from x.
Adjoin z and up to five other distinct off-grid points. The full
induced unit-distance graph has a proper five-coloring with x and z
the same color. Here the grid is L = (1/7) Z[ζ₄₂] in the exact complex coordinates of the pinned G449, with all 449 original sites in L; “off-grid” means outside L. In particular no distance-two original-to-marked
terminal gadget in this off-grid subclass forces the terminal
colors apart. This is stronger in this subclass than ordinary
five-colorability, not an improvement to the whole-plane bound.

## Proof

The previous off-grid degree lemma for this exact G449 says every
off-grid site has at most two original neighbors. Choose a checked
base coloring such that no original neighbor of z has the color
of x, using the explicit pair and simultaneous triple palette
witnesses (or any base palette if z has none). Give z the color of
x. No neighbor of z was x because their distance is not one.

Consider each remaining point's list of available colors after
the base and z are fixed. A point near z, meaning at unit distance
from it, loses at most three colors (two original neighbors and
z), so it has a list of size at least two. A far point loses at
most two, so its list has size at least three. It suffices to show
that the induced graph on the at most five remaining points is
colorable from any lists satisfying these respective bounds.

Suppose otherwise and select an inclusion-minimal uncolorable
induced subset S. Every near point in S has degree at least two,
and every far point degree at least three in S. Indeed, if it
had fewer neighbors than available colors, color the smaller
induced graph and extend greedily.

Two elementary geometric facts are used:

1. Distinct points have at most two common unit neighbors, as
   their unit circles have at most two intersection points.
   The unit-distance graph contains no K4: for two unit-separated
   points, their two common unit neighbors are separated by
   sqrt(3), not 1.
2. On the unit circle centered at z, the only given point's unit
   neighbors have arguments shifted by ±60 degrees. The unit
   chord graph is therefore a disjoint union of subgraphs of
   six-cycles. Any set of at most five points on this circle
   induces a forest.

### Up to four remaining points

If |S|≤3, the minimum-degree bounds exclude any far point;
the near-only induced subgraph is a forest, also contradicting
minimum degree two. Thus |S|=4. Each far point is then universal
in S. With at least three far points, S induces K4, impossible.
With exactly two far points, both near points have the two far
points as common unit neighbors, in addition to z, impossible.
With exactly one far point, the other three points each need a
near neighbor as well as this universal far neighbor. Their
induced forest must then be a path of length two. The two
endpoints already share z and the path's middle as common unit
neighbors, so the far point cannot be adjacent to both. Finally,
with no far point, the induced graph is a forest and fails the
minimum-degree-two condition. This rules out |S|≤4.

### Five remaining points

From now on |S|=5. Two further consequences of the elementary facts
are useful. A far point u that has two *adjacent* near neighbors a,b
cannot have any third near neighbor: z and u are the two common unit
neighbors of a,b, and hence a,b are the two common unit neighbors of
z,u. Also, a near path a–b–c has endpoints a,c with common unit
neighbors z,b, so no far point can neighbor both endpoints.

**Five far.** Minimum degree three on five vertices means the missing
edges form a matching. If it has fewer than two edges, there is a K4.
If it has exactly two edges, their endpoints induce a four-cycle and
the remaining vertex is universal. Such a cycle cannot lie on the
unit circle about the universal vertex.

**Four far.** The four far points induce a graph of minimum degree
at least two. It is either a four-cycle, a diamond (K4 minus one
edge), or K4: the missing edges form a matching. K4 is excluded.
In the four-cycle case every far point needs its third neighbor
at the unique near point, giving a four-cycle on its unit circle.
In the diamond case the two degree-two far points must both neighbor
the near point, but already share the other two far points as common
unit neighbors. Both cases are impossible.

**Three far.** Each of the three far points has at least one far
neighbor, as there are only two near points. If the far subgraph
is a path, its endpoints must both neighbor both near points to
reach degree three. The two near points would then have those two
endpoints and z as common unit neighbors. Hence the far points
form a unit equilateral triangle. Each far point must see at least
one near point, and no near point can see all three (K4).

If both near points see two far points, they cannot see the same
pair (the third far point is already a common neighbor of that
pair). Their far pairs must then be distinct, with one common far
point p. Write the other two far points as q,r. The near points
are the opposite equilateral apices across the pairs p,q and p,r:
in complex coordinates the near points are p+q−r and p+r−q.
Their separation is exactly two and their midpoint is p. Thus
their unique common unit neighbor is p, not z. If the near
points are nonadjacent, each needed at least two far neighbors,
so this case is finished. If the near points are adjacent, each
needs at least one far neighbor; the only remaining possibility
to cover all far points has disjoint far-neighbor sets of sizes
one and two. Name the far triangle u,v,w, with one near point a
seeing u alone and the other b seeing v,w. The location of b
is v+w−u, the other apex over the edge v,w. Thus v,w are already
the two common unit neighbors of u,b. But a needs to be another,
since it is adjacent to both u and b. This is impossible.

**Two far.** If the three near points have no near edge, each
must see both far points, contradicting at most two common
unit neighbors of the far pair. In either remaining near
subgraph there is a near edge, and the far pair must be adjacent:
if not, each far point would need to see all three near points,
including an adjacent pair, which was ruled out above.

If the near subgraph is a two-edge path a–b–c, each far point
must see at least two near points, but neither can see both
endpoints a,c. Since each endpoint needs a far neighbor, the
far points see a,b and b,c respectively. Their positions are
forced as the other equilateral apices across these two edges.
Put z at (0,0), b at (1,0), and a,c at (1/2, ±sqrt(3)/2).
The other apices are (3/2, ±sqrt(3)/2), separated by sqrt(3).
They are not adjacent, a contradiction.

If the near subgraph is a single edge a–b and an isolated point
c, then c must see both far points. Each far point must see one
of a,b as well, and cannot see both, since they are an adjacent
near pair and it already sees c. The points a,b both need a
far neighbor. Label the far points u,v so that u sees a,c and
v sees b,c. The induced graph is exactly the four-cycle
a–b–v–u–a plus c adjacent to u,v. Choose any color for c. Now
each of u,v still has at least two available colors, and a,b
had at least two. An even cycle is colorable from arbitrary
lists of size at least two: shrink to size two; if all lists
coincide, alternate, and otherwise start with a color missing
from the list of a chosen adjacent last vertex, then color in
cyclic order greedily. This colors the putatively uncolorable
subset.

**One far.** Each of the four near points needs a near neighbor.
Their induced forest is then either a four-vertex path or a
pair of disjoint edges. Any three near points contain an
adjacent pair. The far point has degree at least three, but
it cannot have three near neighbors including an adjacent pair.

**Zero far.** The near graph is a forest, impossible with
minimum degree two.

This exhausts all sizes and gives the required extension.

The proof assumes the archived off-grid degree result and the
archived exact palette witnesses, not an unstated plane theorem.
No new computation, solver, or Lean proof was used.

## Tiny next grid experiment (not run)

Existing positive equality witnesses cover all 861 exact
distance-two pairs (x,z) with x original and z an added grid site
having at least two original neighbors. In particular, the
previous census includes 35 pairs with b(z)≥5 (21 with b=5 and
14 with b=6, all nonreflected). These are a small prioritized
fixture because more original adjacencies can constrain the
terminal's permitted color. This is only a deterministic
priority, not evidence of forced difference.

Take only these 35 marked pairs initially. Filter a second grid
point w distinct from both terminals and outside the original
449 sites. If w is not adjacent to z and b(w)≤4, or if w is
adjacent to z and b(w)≤3, any positive equality palette for
(x,z) extends greedily. Thus it suffices in this fixture to
check at most 35 × 1,043 = 36,505 cases using the exact degree≥4
site list (degree≥5 for the nonadjacent branch).

For palette index k, let Lk(v) be the complement in the five
colors of the colors at v's exact original neighbors. For each
marked pair, form masks A(c) grouped by terminal color: in
color group c retain k exactly when palette k gives x color c
and c∈Lk(z). For each w, form mask B(w) that Lk(w) is nonempty
and masks Bc(w) that it contains a color other than c. If w is
nonadjacent to z, intersect the union over c of A(c) with B(w).
If adjacent, test the union over c of A(c)∩Bc(w). A positive
result has an explicit k, shared terminal color c and catalyst
color, checked on the exact neighbor lists and possible new
edge. Algebraic position and candidate edge are verified
using the independently reconstructed exact denominator-seven
unit-direction table. The residual transcript should record
exact x/z/w coordinates, original incidence, and all palette
masks. Stop and report a gap without claiming forced difference.
Any true forcing test would need a separately authorized complete
equality-imposed graph-coloring refutation with a checked
certificate. This staged experiment was not run.
