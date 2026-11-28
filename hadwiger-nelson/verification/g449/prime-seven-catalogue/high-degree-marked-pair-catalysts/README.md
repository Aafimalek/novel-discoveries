# A catalyst cannot force apart these 35 high-degree terminal pairs

Fix a pair (x,z) from the earlier exact census, with x an original
G449 vertex and z a site in (1/7) Z[ζ₄₂] at distance two from x,
having at least five original neighbors. There are exactly 35
such pairs, all non-reflected: 21 have five original neighbors,
and 14 have six. For **every** additional point w in the plane,
distinct from all original points and z, the graph on G449, z,
and w has a proper five-coloring with x and z the same color.

The earlier single-terminal check supplies a palette with equal
terminal colors. If w is off-grid, the published off-grid-degree
lemma gives at most two original neighbors: even adjoining a
fixed z color leaves at least two choices for w. If w is on-grid
and has at most three original neighbors, any such palette leaves
at least one choice for w. The same applies if w has four
original neighbors and is not adjacent to z. The remaining site
set is contained in the earlier exact list of 1,043 grid sites
with at least four original neighbors.

We checked the full 35 × 1,043 product in this list rather than
omitting the nonadjacent degree-four sites. Both coordinate and
61-list profile inputs are pinned. We directly recomputed each
original-neighbor list from the independently validated exact
grid unit direction catalogue and checked all five-bit available
color lists against the pinned profile. We recomputed integer
Laurent norm remainders for each selected terminal and independently
checked them for every z,w pair against its unit-direction
classification. All 61 archived base color vectors were checked
for properness on the exact Euclidean unit graph.

For each terminal color c, A(c) is the set of palette indices
giving x color c while leaving c free at z. B is the set of
palette indices with any free color at w. B(c) is the set with
a free color at w different from c. At nonadjacent w,z check
(union of all A(c)) intersect B. At adjacent w,z check the
union over c of A(c) intersect B(c). If nonempty, take one set
bit, then check the resulting explicit terminal and catalyst
colors against all new edges, independent of that bitset test.

Exact counts: 36,505 raw pairs; 35 collisions (w=z), 105 adjacent
non-collisions and 36,365 nonadjacent non-collisions. All 36,470
non-collisions have a checked equality witness. There are zero
residuals. The positive witness JSONL has records
`[original_x, grid_z, grid_w, palette_index, shared_color, w_color]`.
The grid IDs and palette indices are zero-based. A nonempty
residual file, had it occurred, would not prove forced difference.

## Replay

The source and exact inputs are in the accompanying archive. Extract
into a fresh directory and run `bash replay.sh`. This checks all
archived files, runs one standard-library Python worker under the
published guards, and compares all 36,470 positive witnesses byte for
byte. The original G449 data and earlier palette bank are included
as exact pinned inputs. The prior [off-grid degree lemma](https://github.com/Aafimalek/novel-discoveries/tree/487e4dfc1f1bcbd536a4d03c814db4d0d65da779/hadwiger-nelson/verification/g449/prime-seven-catalogue/one-point-distance2-terminals)
allows the extension from this finite exact check to a catalyst
anywhere in the plane for these same 35 marked pairs. This finds
no forced-difference gadget, and makes no claim for other marked
terminal pairs or the chromatic number of the plane. No Lean or SAT
was used. The computation and writing were developed with AI
assistance.
