# Six all-grid additions: the unique base-degree-one vertex is universal

**Verified.** Given the preceding five-point theorem, six distinct grid
additions preserve five-colorability when the unique base-degree-one
new point is adjacent to all five other new points. All 32 replay
shards completed, under a hard 132,000 KiB virtual-memory limit.
There were 1,350,118 raw rim choices and 5,208 configurations passing
the minimum-total-degree condition. The existing bank covers all
5,208 (only its first 18 palettes were needed). Zero residuals remained,
and no solver was used. This package does not treat a unique
base-degree-one vertex with only four new neighbors, or any other
unresolved six-point branch.

[Paper (PDF)](paper/g449-six-one-universal.pdf) · [TeX](paper/g449-six-one-universal.tex) · [Exact replay archive](one-universal-replay.tar.gz)

An independent fresh replay regenerated the input and matched all 32 archived receipts.

## Derivation

Assume the prior theorem that any five points can be added to G449
with five colors. For a new vertex $v$ let $b(v)$ be its number of
original neighbors and $d_H(v)$ its degree among the six additions.
A counterexample must have
[
\delta_{\rm add}=\min_v(b(v)+d_H(v))\ge5
]
by deleting and greedily restoring a vertex of smaller total degree.

In the checked subcase the unique vertex $h$ with $b(h)=1$ is
adjacent to all five other new vertices. All other vertices have
$b\ge2$: another degree-one vertex is outside the case, and a
degree-zero vertex would also be universal in a putative counterexample
and share at least three unit neighbors with $h$, impossible.
The 7,056 possible rim points have $b\ge2$; enumerate the 546 exact
signed grid steps from each, in total 3,852,576 incidences. Retain
only hub points with exactly one original neighbor, storing its
original index from the complete coordinate lookup. All incidences
at a hub enter the same shard. The earlier independent degree-one
incidence histogram predicts 109,683 retained incidences on 30,233
hubs, 9,394 hubs with at least five rims, and 1,350,118 raw five-rim
choices. The collector checks these aggregate counts.

On the hub's unit circle the available rim graph has maximum
degree two and components of at most six vertices (unit chords
move by $\pm60^\circ$). A selected rim requires
$b(v)+d_{\rm rim}(v)\ge4$. Peel any rim vertex that fails even in
the full remaining rim graph; then enumerate eligible subsets in
each component and combine them to size five, as in the already
checked degree-zero universal-hub verifier. For each proper base
palette, forbid the hub's unique original neighbor's color.
For each other hub color in turn, forbid that color at all rim
vertices in addition to the colors of their respective base
neighbors. Run exact finite list search. No solver is called, and
a bank residual is only an uncolored configuration under those
palettes, not a counterexample.

The generator checks all exact input hashes, regenerates the
complete signed catalogue and verifies all base palettes against
the induced base graph. C++ reads all 12 coefficients, validates
injective additive packing using explicit bounds, recomputes exact
neighbor groups, checks base edges and palettes, sharded incidence
counts, and checks all emitted rim degrees. It has the same hard
incidence/visit/output caps as the degree-zero verifier. The collector
rejects any missing or incomplete shard; by default the clean replay
stops at the first nonempty residual.

## Clean replay

```sh
PYTHONPATH=PATH_TO_AUDIT_LAYERS_AND_TWO_POINT_REPLAY timeout 30s ./replay.sh \
  PINNED_G449_INPUT_DIR denominator-seven-directions.tsv \
  extension-witnesses.json triple-residual-witness.json \
  four-witness.json five-witness.json FRESH_RUN_DIR
```

This uses GNU C++20, Python 3.10+, NumPy, and a hard 132,000 KiB
virtual-memory limit. It uses the same exact pinned inputs as the
degree-zero universal-hub replay (their SHA-256 values are in
`INPUTS.sha256`). Helper scripts, catalogue, and first two witnesses
are in the working checkout's `g449-mod7-work/`; locally the four-
and five-point witness paths are `/tmp/g449-four-five-release/four-witness.json`
and `/tmp/g449-five-release/five-witness.json`. The pinned G449 input
directory is locally `/tmp/hadwiger-g449`.

The full 32 shard logs and empty residual files are in `checked/`.
Static receipt verification uses `sha256sum -c CHECKED.sha256` and
`python3 collect.py checked 32 --expect-closed`.

## Separate nonuniversal case: outline only

If the unique degree-one point $h$ has new degree four, take its four
exact grid rim neighbors $R$ and the one missed vertex $w$. The latter
is not adjacent to $h$ and can see at most two points of $R$,
since otherwise $h,w$ have at least three common unit neighbors.
In a putative obstruction $b(w)\ge 5-|N(w)\cap R|\ge3$.
For a rim point, first require $b(v)+d_R(v)\ge3$; equality means
$w$ must be adjacent to $v$. More than two required neighbors
is immediately impossible. The short enumeration would split by
$|N(w)\cap R|$:
- Zero: $b(w)\ge5$ and no required rims. Group the prospective
  isolated vertices by their support bitsets over the verified palettes.
- One: $b(w)\ge4$; generate $w$ from the union of exact rim-neighbor
  sets and check that exactly one contact occurs.
- Two: $b(w)\ge3$; generate from pairwise intersections of exact
  rim-neighbor sets, with a canonical rim pair to avoid duplicates.

In each branch additionally reject points already in the six,
adjacent to $h$, or with a missing required rim contact. This
outline has not been implemented or replayed.
