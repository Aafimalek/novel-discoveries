# Four patches joined at their centers remain four-chromatic

This is an exact negative control for the
[three-copy pole construction](../three-copy-pole-control/README.md),
not a plane bound. We independently checked the 88-site
graph at depth one and analyzed every interpatch pair
symbolically for nonzero rational B at the six specified k
values 2, 22, 722, 472, 16722, 4222. No SAT, Lean, or Git ran.

## Unit rhombus and exact finite graph

Let K=Q(√33,√−3), ρ=(31+3√−7)/32, c=31/32 and T=2c.
Use the native pole coordinates x,y from the sibling
construction, and let z=Ty−x. The four centers are

    y,  ρx,  ρz,  ρ²y.

Because 1+ρ²=Tρ, the first and last have the same
midpoint as the two middle centers. Reflecting the
two original unit edges through this common midpoint
gives the two further unit edges. At the pinned sample
B=512/25, the four centers are distinct, both diagonals
are nonunit, the native z has valuation 11 at 2, and
the minimum of its rational-basis 5-valuations is −1.
The ratio of the two distinct edge directions of the
rhombus is integral in the mod-5 coefficient ring.
The whole patched graph still escapes the rotation-invariant
mod-5 screen because its original 24-point subgraph did.

Use the 22 ordered native offsets P recovered in
published coordinate-row order from the exact 24-point
patch. The replay independently reconstructs P as W+W
union the native Moser spindle. The four sets of actual
sites, ordered as listed, are

    y+P,  ρ(x+P),  ρ(z+P),  ρ²(y+P).

For B=512/25 all 3,828 pairs agree between the two exact
norm formulas. There are 88 distinct sites and 196 unit
edges: 48 within each patch, and the four interpatch
edges (10,32), (10,54), (32,76), (54,76) in the zero-based
order above. Every interpatch edge meets only patch centers.

For a proper four-coloring, use the four native residue
colors on each patch and permute those colors so that the
two outer centers share one color and the two middle centers
share a different color. The induced graph contains an exact
seven-site, eleven-edge Moser spindle. The replay fixes its
first color to zero and rejects all 729 assignments of three
colors to its other six vertices. Therefore the graph has
chromatic number **exactly four**.

This is an instance of the general center-only rule: if every
patch has just one site participating in any interpatch edge,
then the chromatic number is the maximum of the individual
patch chromatic numbers and the chromatic number of the graph
of their marked sites. After coloring each separately, use
independent color permutations on the patches to match their
marked sites to the latter coloring. Merely a longer cycle of
the same center-only design cannot improve the bound here.

## Complete all-rational parameter audit for the six k values

Use U=63/992+k√33 B and C=1−c². In the exact multiquadratic
basis below write the common denominator and numerators as

    D = U²+C−3B²+2UB√−3,
    X = 2U,
    Y = 2cU+U²−C+3B²,
    Z = 2cY−X.

Then x=X/D, y=Y/D and z=Z/D. The denominator never vanishes
for nonzero rational B at these fixed k: U≠0 by irrationality
of √33 and the imaginary coefficient 2UB√−3 is nonzero.
For any p in P, the ambient numerator in patch i is
the corresponding rotation times (Dp+A), with center
numerator A chosen from (Y,X,Z,Y).

For each pair in distinct patches, let N be the difference
of its two ambient numerator rows. A coincidence requires
every coordinate polynomial of N to vanish. Unit distance
requires every coordinate polynomial of N·conj(N)−D·conj(D)
to vanish. The latter degree is at most four. The checker
clears one common rational coefficient denominator, ignores
identically zero coefficient polynomials, and removes powers
of B from each remaining row (the domain excludes B=0).
The subsequent polynomial GCD is computed by exact
primitive integer pseudo-remainders, equivalent to the
rational GCD up to nonzero scaling. There is no modular
sieve or matching assumption in this replay.

For **each** of the six fixed k values, all 2,904 interpatch
pairs were tested both ways:

| equation | all zero | constant GCD | nonconstant GCD |
|---|---:|---:|---:|
| Unit distance | 4 | 2,804 | 96 |
| Coincidence | 0 | 2,882 | 22 |

Every nonconstant GCD is the monic quadratic
B²−21/[961(11k²+1)], only between the two middle patches.
A rational root would give 11k²+1=21q² with q=1/(31B)
rational. At 11, the left side and 21 are units, so q is
a unit; reduction would give q²=−1 mod 11, impossible.
Thus all 88 points stay distinct and all interpatch edges
remain exactly the four center edges for **every nonzero
rational B at those six fixed k values**. This is stronger
in B than merely varying the admissible pole parameter ℓ,
but does not cover arbitrary k, different patches,
irrational parameter choices, or other couplings. For
any of the audited rational parameters the unchanged patch
graphs and center-only rule give the same exact chromatic
number four.

The separate [written native-link classification](NATIVE-LINK.md)
addresses a different geometric question; it is not needed
for the finite polynomial result.

## Reproduction
The full exact graph and pair-by-pair audit are in
`verified/exact-artifacts.tar.gz`. Unpack with
`tar -xzf verified/exact-artifacts.tar.gz` before comparing regenerated files.


```sh
mkdir -p overlay-tmp
export TMPDIR="$PWD/overlay-tmp"
export PYTHONDONTWRITEBYTECODE=1
(ulimit -v 132000; timeout 90s python3 replay.py \
  ../three-copy-finite-stress/fixture.py \
  ../three-copy-saturation-150/replay.py \
  ../three-copy-pole-control/replay.py \
  ../three-copy-pole-control/verified/exact-24.json \
  ../three-copy-pole-control/verified/samples.json NEW_OUTPUT)
cmp NEW_OUTPUT/exact-88.json verified/exact-88.json
cmp NEW_OUTPUT/pairwise-polynomials.json verified/pairwise-polynomials.json
cmp NEW_OUTPUT/summary.json verified/summary.json
```

The replay pins the source and input hashes. The final
guarded run took 4.297 s. A preliminary local attempt
caught a sign-normalization issue for a single constant
GCD and produced no certificate; it was corrected before
the final replay. Both invocations combined took under 8 s.
