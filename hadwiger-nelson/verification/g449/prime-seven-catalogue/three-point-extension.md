# Any three-point extension of G449 is five-colorable

Aafi Khan Malek, independent researcher, Ahmedabad, India · [aafimalek2032@gmail.com](mailto:aafimalek2032@gmail.com)

Add any three distinct points anywhere in the Euclidean plane to the published 449 points of [Heule and Przybocki's G449](https://arxiv.org/abs/2611.28518). The induced unit-distance graph is still five-colorable. The result includes one- and two-point extensions. It is a restriction on this starting graph, not a new bound for the plane. The finite proof here is exact computational verification, not Lean.

[Paper PDF](paper/three-point-extensions.pdf) · [TeX source](paper/three-point-extensions.tex)

## A point off the grid has at most two base neighbors

Write $\zeta=e^{2\pi i/42}$ and let the grid be $\tfrac17\mathbb Z[\zeta]$. The [complete direction catalogue](README.md) gives 546 signed grid unit displacements. Translating them from each published point gives all grid points with a base neighbor, including 229,320 outside points. Among that list (including the original points as possible centers), **97,650** different triples of base vertices share a grid center.

Distinct neighbors of any point on its unit circle cannot contain a collinear triple. For a triple of base points, write $A,B,C$ for their numerators over denominator 7 and put $u=B-A$, $v=C-A$, $U=u\bar u$, $V=v\bar v$, $W=(u-v)\overline{(u-v)}$, and $D=u\bar v-\bar u v$. Unit circumradius implies $UVW+49D^2=0$. The replay checks this necessary equality modulo primes 43, 127, 211, 337, 379, 463, and 547 at a primitive 42nd root and its inverse. All **14,985,824** unordered base triples are included, and every one of the **97,650** survivors already has a grid center. A noncollinear triple has a unique circumcenter. Thus a point outside the grid cannot be a unit neighbor of three base points.

## Two points

If one added point is outside the grid, or is a grid point with at most three base neighbors, first color the other point using the checked one-point theorem. Finish greedily: the last point has at most four colored neighbors. The remaining grid pairs belong to the **1,043** candidate vertices with at least four base neighbors. Check all **543,403** unordered pairs with the 35 base colorings (the supplied G449 coloring and the restrictions of the 34 previously checked one-point witnesses). For a base coloring let $A,B$ be the sets of colors not used on each added point's base neighbors. A pair can be colored if both lists are nonempty and, for a connecting edge, they are not the same singleton. The original coloring fails in 34,911 pairs, including 44 adjacent pairs with two nonempty lists. The 35-coloring bank covers all pairs.

## Three points

If one added point is off-grid or has at most two base neighbors, color the other two first. The last sees at most four colored neighbors. Otherwise the three belong to the **2,429** grid candidates with at least three base neighbors. For the small graph induced by the three new points:

- **No edges.** If a vertex has at most four base neighbors, color the other pair and assign any missing color to that vertex. Otherwise all have degree at least five into the base. A triple missed by the original coloring must include one of the 34 one-point exceptions. Group the other candidates by the subset of the 35 colorings where they have a nonempty list; the triples not covered by the bank can then be enumerated exactly.
- **One edge.** First check each candidate edge across the color bank. An isolated third vertex with at most four base neighbors can always be colored. For a higher-degree third vertex intersect its nonempty-list subset with the subset where the edge can be colored.
- **Two edges.** The three vertices form an induced path. Both leaves need nonempty lists. A center color works unless one of those leaves has exactly that singleton as its list.
- **Three edges.** Hall's condition for the three lists is exact: each list is nonempty, every pair of lists has union size at least two, and the total union has size at least three.

The candidate graph has 7,777 edges, 50,995 induced paths, and 721 triangles. The bank leaves exactly **60** triples: 21 edgeless, 38 with one edge, and one path. The union of their 54 added vertices with G449 is a **503-vertex graph with 2,545 exact unit edges**. One checked five-coloring of this graph covers all 60 cases. The witness is shipped, so the replay uses no solver. An independent check recomputes every one of its 126,253 pairwise distances by Laurent-polynomial reduction and verifies the list rules against all possible masks.

## Replay

Use the same pinned input files as the [catalogue audit](README.md). With Python and NumPy:
~~~sh
python3 two_point_replay.py INPUT_DIR denominator-seven-directions.tsv extension-witnesses.json
python3 check_grid_triples.py INPUT_DIR denominator-seven-directions.tsv extension-witnesses.json --residual triple-residual-witness.json
python3 independent_triple_audit.py INPUT_DIR denominator-seven-directions.tsv triple-residual-witness.json
~~~
Only the optional witness search with check_grid_triples.py --solver uses CaDiCaL; the commands above replay exact arithmetic and check the stored color vectors. No new plane bound, formal Lean check, or claim about four or more new points is made.
