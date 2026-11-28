# Six grid points of which at least two have base degree one

This is one exact subcase of the six-point G449 problem. It assumes the
preceding theorem that every five-point extension of G449 is
five-colorable. No six-point case with fewer than two base-degree-one
points is decided here.

Let $b(v)$ be the number of original neighbors and $d_H(v)$ the degree
in the new six-point graph $H$. Write
$$
\delta_{\mathrm{add}}=\min_{v\in V(H)} (b(v)+d_H(v)).
$$
A failing extension would have $\delta_{\mathrm{add}}\ge5$: upon
deleting a vertex with at most four total neighbors, color the
remaining extension by the five-point theorem and give the deleted
vertex an unused color.

## Replay

Use Python 3 and NumPy, assertions enabled, with `audit_layers.py`
and `two_point_replay.py` beside this script or on `PYTHONPATH`:

```sh
python3 multiple_degree_one.py PATH_TO_PINNED_G449_INPUTS \
  denominator-seven-directions.tsv
```

Input hashes, full 546 signed direction catalogue, and base edges
are verified by the imported replay. Residue filters only reject
candidate pairs; final distances use exact cyclotomic arithmetic.
No SAT, Lean, or precomputed color vectors are needed.

## Completeness

Every base-degree-one vertex must have at least four new neighbors.
Any two such vertices are adjacent: if not, both see the other four
new vertices, but two distinct points have at most two common unit
neighbors. Neither can be universal because then they would share
at least three common neighbors. Hence each has new degree four.
There can be at most three such vertices, since no unit $K_4$
exists. Nor can any of the other vertices have base degree zero:
such a vertex would have to be universal, and would share at least
three common neighbors with a base-degree-one vertex.

**Exactly two.** The vertices share exactly two new neighbors, since
each is adjacent to the other and to three of the four remaining new
vertices. The two common neighbors are the opposite equilateral
apices at distance $\sqrt3$. The other two vertices each have base
degree at least two and are private neighbors, one for each center.
Enumerate all 24,890,040 pairs from the 7,056 grid points with base
degree at least two. Exactly 5,691 pairs have distance $\sqrt3$.
For scaled coordinates $A,B$, their two common unit centers have
scaled coordinates
$$
(2A+B+\eta(B-A))/3,\qquad (A+2B-\eta(B-A))/3,
\qquad \eta=\zeta_{42}^{7}.
$$
Only 21 pairs of these centers both have base degree one. For each
of those pairs enumerate the Cartesian product of its two exact
private-neighbor sets (using all signed grid directions). Each of
the 1,967 completions has $\delta_{\mathrm{add}}<5$.

**Exactly three.** The three base-degree-one vertices make a unit
triangle, and each sees two of the remaining three vertices. Each
pair already shares the third base-degree-one vertex, so its two
size-two sets of remaining neighbors must intersect in exactly
one vertex. The three high vertices are therefore the three exterior
equilateral apices of the low triangle. They make a side-two
equilateral triangle, with the lows as side midpoints. Each apex
has no edges to the other apices (distance two), so it has new
degree two and must have at least three base neighbors. Among the
2,429 grid vertices with base degree at least three there are 637
exact distance-two pairs and 21 equilateral triangles of side two.
None has all three side midpoints of grid base degree one.
