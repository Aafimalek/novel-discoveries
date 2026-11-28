# Six-point off-grid steps around G449

Here $L=(1/7)\mathbb Z[\zeta_{42}]$ is the denominator-seven grid in
the published G449 embedding. Assume the exact five-point extension
theorem for G449 from the [preceding work](../five-point-extensions/).
Then **every extension by six points with at least one off-grid point
preserves five-colorability**. The all-grid case is not addressed.
This is not a new bound on the entire plane.

[Paper (PDF)](paper/six-off-grid-extensions.pdf) · [TeX](paper/six-off-grid-extensions.tex)

### Reproduce

Obtain `G449.k21` and `G449.s6` from the
[original authors' pinned commit](https://github.com/bprzybocki/G449/tree/125bfda97ed1d336f84694de04dedcfb349c5164).
From this directory, with Python 3.10+, NumPy, and assertions enabled:

```sh
sha256sum --strict -c SHA256SUMS
export PYTHONPATH="../:../four-five-point-extensions${PYTHONPATH:+:$PYTHONPATH}"
python3 high_triples.py PATH_TO_PINNED_G449_INPUTS ../denominator-seven-directions.tsv
python3 mixed_shapes.py
python3 exterior_apex.py PATH_TO_PINNED_G449_INPUTS ../denominator-seven-directions.tsv
python3 two_off_apices.py PATH_TO_PINNED_G449_INPUTS ../denominator-seven-directions.tsv
```

The geometry helpers check the published file hashes, regenerate
and validate the catalogue and match the complete original graph.
All computations here use exact integers; no SAT solver or Lean.

## Geometry and mixed lemmas

The previous exact checks give (I) every off-grid point has at most
two original neighbors, (II) one with two original neighbors is not
adjacent to any new grid vertex with at least three original
neighbors, and (III) one with at least one original neighbor is not
adjacent to two new grid vertices with at least four original
neighbors. For (II) see [the four-point checker](../four-five-point-extensions/classify_offgrid_four.py);
for (III) see [the mixed-five-point checker](../four-five-point-extensions/one_base_high_pair.py). Any two points have at most two common unit
neighbors. The grid neighbors of an off-grid point are independent:
both equilateral apices of a grid unit segment lie in the grid.

A fourth exact observation is (IV): an off-grid point cannot be
adjacent to three new grid vertices with at least four original
neighbors. There are 1,043 such grid vertices. The grid direction
catalogue produces all grid common centers of their triples.
Of 188,560,841 unordered triples, 186,404,358 are pairwise
nonadjacent, the only triples that could have an off-grid center.
For a triple on a unit circle the scaled circumradius identity
$UVW+49D^2=0$ is necessary. The same four justified residue checks
as before (43, 127, 211, 337) leave exactly 133,371 triples, all with
a verified grid center. Uniqueness of a noncollinear circumcenter
proves (IV).

## One off-grid point among six

In a failing six-point extension, deleting any one new point
leaves a five-colorable graph. Every new vertex thus has total
degree at least five. By (I), an off-grid point $x$ has at least
three new neighbors. If there is just one off-grid point, its new
neighbors are independent.
- If there are three, $x$ has exactly two base neighbors. By (II)
  its three new neighbors each have base degree at most two.
  Each must then see both of the remaining grid vertices to
  achieve total degree at least five, contrary to the common
  neighbor bound.
- If there are four, they each have base degree at least three
  (only $x$ and the remaining grid point are possible new
  neighbors), so $x$ has exactly one base neighbor by (II).
  By (III) at least three of them have base degree exactly three.
  These three all require adjacency to the remaining grid point,
  which would then have three common neighbors with $x$.
- If there are five, all five have base degree at least four,
  contrary to (IV).

## Finite shape and prism pruning

The shape checker exhausts the $2^{15}$ possible labeled new
graphs on six points for each fixed number of off-grid labels.
At each vertex the graph induced by its neighbors has degree
at most two and no cycle, since unit edges on its unit circle
follow angles $\pm60^\circ$ and here that circle has at most five
of the six new points. Use the common-neighbor bound, the
independence of grid neighbors of every off-grid point, (I)–(IV)
and the elementary lower bound $5-d$ on base degree for any
new vertex with new degree $d$.

Two further geometric rules:
- Any realized unit triangular prism on six distinct points
  consists of two translates of an equilateral triangle, matching
  by translation. For an orientation-preserving correspondence,
  center the first triangle at zero and write the second
  $t+Ra_i$. If $R\ne I$, the condition that
  $|t+(R-I)a_i|$ be independent of $i$ forces $t=0$, since
  $R-I$ is invertible and the $a_i$ span affinely. A unit
  matching distance then means $R$ rotates by $\pm120^\circ$
  and the point sets coincide. For an orientation-reversing
  correspondence let the normal to the reflection axis be
  vertical. Equality of the three matching distances allows
  at most two different normal projections of the $a_i$;
  two $a_i$ must share a projection. Thus the axis is parallel
  to their side; set them at $(\pm1/2,0)$ and the third
  at $(0,\sqrt3/2)$. The matching distances give
  $|t|=|t-(0,\sqrt3)|=1$, so $t=(\pm1/2,\sqrt3/2)$,
  again with coincidences. Hence only translation remains.
  If one triangle is entirely in the grid and one point
  of the other lies in the grid, the translation is a
  grid displacement and both triangles are entirely in the grid.
- Distinct exterior apices of one equilateral unit triangle,
  of forms $a+b-c$ and $a+c-b$ up to relabeling, are at
  distance two. Their unique common unit neighbor is their
  midpoint $a$; no other new vertex can meet both.

In every surviving prism with three or more off-grid points,
each grid vertex has an off-grid neighbor. Every prism vertex has
new degree three, so its off-grid vertices have two original
neighbors by minimum total degree and (I); all adjacent grid
vertices have base degree at most two by (II). With any proper
base coloring, all three or more remaining colors at each vertex
suffice for the prism. To prove 3-list-colorability, trim all
lists to exactly three. If all lists agree, assign distinct
colors on the first triangle and cyclically shift them for the
matching second triangle. Otherwise choose adjacent $u,v$ with
different lists and give $u$ a color absent from $v$. The
prism minus $u$ is connected. Color it greedily in reverse
spanning-tree order rooted at $v$; each nonroot has its
parent still uncolored, and at the root the already colored
$u$ contributes no forbidden color in its list.
After these steps the shape counts for 1 through 6 off-grid
points, up to type-preserving relabeling, are $0,4,1,0,0,0$.


## Remaining two and three off-grid shapes

For exactly two off-grid points, every remaining graph has the
two off-grid points adjacent and sharing two grid vertices whose
new degree is at most three. These two grid vertices thus have
base degree at least two and are the opposite equilateral apices,
at distance $\sqrt3$. There are 7,056 new grid vertices with base
degree at least two. Out of their 24,890,040 pairs, exact polynomial
arithmetic after necessary modular filters finds 5,691 at this
distance. With scaled grid numerators $A,B$, the two common unit
centers in the same scaling are
$$
(2A+B+\eta(B-A))/3,\qquad (A+2B-\eta(B-A))/3,
\qquad \eta=\zeta_{42}^7.
$$
The formula is the midpoint plus or minus a perpendicular
offset of length $1/2$ for the unscaled segment of length
$\sqrt3$. The checker finds both numerators coefficientwise
divisible by three in every one of the 5,691 pairs and checks
all required distances exactly. Hence both common centers
are grid points, contrary to the remaining shapes.

For exactly three off-grid points, the only remaining shape is
an off-grid equilateral unit triangle together with its three
exterior grid apices. The apices have new degree two and therefore
base degree at least three. They form a side-two equilateral
triangle, whose side midpoints are the three off-grid vertices.
Each off-grid vertex has new degree four and must have a base
neighbor. The 2,429 new grid vertices with base degree at least
three give 2,948,806 pairs. The exact checker finds 637 distance-two
pairs and 21 side-two equilateral triangles; 14 of these have three
off-grid side midpoints, and none has a base neighbor at every
midpoint. This closes the last remaining off-grid shape.
