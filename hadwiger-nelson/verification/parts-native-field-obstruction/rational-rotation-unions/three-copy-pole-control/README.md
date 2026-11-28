# Pole-escaping cross edges and a checked 24-point control

There are exact cross-copy unit edges of every positive
coefficient-wise 5-pole order in the three-copy ambient
set K ∪ ρK ∪ ρ²K, for K=Q(√33,√−3) and
ρ=(31+3√−7)/32. This clears the necessary
[mod-5 displacement filter](../three-copy-saturation-150/README.md);
it does not imply a chromatic lower bound. The first
translated-patch control still has an explicit five-coloring.

## Construction and exact edge identity

Write r=√33, s=√−3, c=31/32, C=1−c²=63/1024,
T=31/16, and U₀=63/992. Choose depth m≥1, an even integer
k with k≡2 mod 5 and v₅(11k²+1)=m, and positive ℓ prime
to 10. Such k exists: 2 is a simple root of 11X²+1 mod 5,
so lift it to a root mod 5^m. Choose a next digit other
than the unique root extension to get exact valuation m,
and add 5^(m+1) if needed to make the result even.

Set

    B=512/(5^(2m) ℓ),  U=U₀+kBr,
    V=(C−3B²)/U,      A=(U+V)/2,
    t=c+(U−V)/2,      Z=A+Bs,
    x=1/Z,            y=tx.

The valuations below ensure U,Z are nonzero. From
A²−(t−c)²=UV=C−3B², one obtains
N(Z)=A²+3B²=t²−2ct+1. As y=t x with t real,
both distances from ρx to y and to ρ²y are exactly one.
The outer two points are not adjacent: their squared
distance is N(y) times 63/256, which has 2-adic
valuation −8 by the computation below.

## Exact local scopes

At 5, Q₅(r) is unramified quadratic and contains a root
s₅ of −3 with s₅≡2r modulo 5. Indeed s₅/r is the simple
lift of the root 2 of 11X²+1. The two evaluations s↦±s₅
are distinct local branches; they must not be conflated.
The factor kr+s₅ is a unit, so from
(kr)²−s₅²=3(11k²+1) we get v₅(kr−s₅)=m.
At this place C,c,U₀ have valuation zero, B has
valuation −2m, and U has valuation −2m.

Let w=U−Bs₅. Since U₀ is integral and
B(kr−s₅) has valuation −m, v₅(w)=−m. The exact identity

    A−Bs₅ = (w²+C)/(2U)

gives valuation zero. The other branch A+Bs₅ differs by
2Bs₅ and has valuation −2m. From t=c+w−(A−Bs₅),
v₅(t)=−m. Thus the split valuations of x are (0,2m)
and of y are (−m,m), in the order s↦−s₅,+s₅.

The change of basis between A,B and the two split
values A±Bs₅ is invertible over the local valuation
ring because 2s₅ is a unit. The valuation of a
Q(r) element in the chosen unramified extension
equals the minimum valuation of its 1,r coefficients;
this follows from the independent residue basis.
Hence the minimum rational-coefficient valuation
of x is exactly zero and of y exactly −m in the
bitmask basis. Multiplication by ρ or ρ² preserves
this minimum, since rotations and inverses both have
integral coefficient matrices at 5. Subtracting the
integral ρx cannot cancel the pole in either cross
displacement. The real Cartesian radical coordinates
differ from this basis only by reordering, signs,
and factors of three, which are units at 5. Therefore
both cross unit displacements have exact pole order m
for the coefficient-integrality criterion.

At 2, use the native embedding with r≡1 mod 4 and
s in the unramified quadratic extension, so v₂(r)=v₂(s)=0.
Here v₂(B)=9, v₂(U₀)=−5, v₂(C)=−10 and
v₂(U−U₀)≥10. In V−C/U₀ the two summands
C(1/U−1/U₀) and −3B²/U have valuations at least 10
and 23, respectively. At B=0, A=t=1/T=16/31.
Consequently both A and t differ from 1/T by
valuation at least 9. This gives

    v₂(x)=−4,   v₂(y)=0,
    v₂(x−T)≥1, v₂(y−1)≥5.

In the first case m=1,k=2,ℓ=1 the two inequalities
are equalities. At the real place, for fixed m,k, taking
ℓ through arbitrarily large positive integers prime to
10 sends B to zero and (x,y) to (T,1), by continuity of
the rational formulas where their limiting denominators
are nonzero. It does not change the exact unit equations
or the 5-pole order.

The same calculation can perturb a previously valid pair
of parameters U*,B* (U* and the old Z nonzero). For a
fixed adjacent or extreme ratio, add β to B* and krβ to
U*, where β=2^N/(5^(2m)ℓ). Choose m large enough that both
new terms dominate the old terms in U and U−Bs₅ at 5,
then choose N large enough for any fixed native 2-adic
precision, and ℓ large for real closeness. This preserves
the individual unit equation and can preserve the old
residue-cell labels. It does not preserve an extra
unit connection between two independently perturbed
vertices or a common landing point.

## Exact replay and the 24-point control

The replay checked all depths 1 through 6 for
k=2,22,722,472,16722,4222, each at both ℓ=1 and ℓ=101.
It independently evaluates the two 5-adic branches
by lifting s₅/r and bounding the approximation error.
It also verifies the integer coefficient valuations,
the stated 2-adic bounds, and the exact two edge
identities in both norm formulas.

For m=1,k=2,ℓ=1 translate the 22-point native patch
W+W union the Moser spindle to x on the middle copy
and include the two outer points. Full geometry:
24 distinct sites, 276 unordered pair checks, 50
unit edges. Both other copies are checked for each
native patch point (44 exact discriminant tests).
The only higher attachments are the two intended ones
from its center. The four native residue colors on
the translated middle patch, with a shared fifth
color for the two nonadjacent outer points, give
an exact checked proper coloring of all 50 edges.
Color class sizes are 7,5,5,5,2.

### Coupling cautions

Multiplying edges by ρ or ρ⁻¹ gives a shared higher
target ρy for x and ρ²x. For the six marked vertices
x,ρx,ρ²x,y,ρy,ρ²y the exact checked graph is just
two disjoint 2-edge stars, at each of the 12 samples.
All their four edges escape the coefficient filter,
but the symmetry alone is not an additional coupling.

Two distinct negative sources in a fixed copy cannot
share a higher endpoint in one other fixed copy.
If the level offset is h>0 and the native target
has valuation b, then b<h for a negative source.
The reversed ratios from target to the two sources
would both have valuation −h; their product would
have valuation −2h. But that product is
1−1/N(target), whose valuation is at least
min(0,−2b)>−2h. This contradiction does not rule
out targets shared across *different* source copies.

Even two different separations can share a pole-escaping
target for a purely congruence-based reason. If η∈K is a
unit with a 5-pole (for example (−49+rs)/50), then the old
anchor target ρ² and sources ρ^i·2Re(ρ^(2−i)) for i=0,1
can all be multiplied by η. The new edge displacements
are exactly ηρ^(2i−2). They have the same pole and their
entire graph is merely rotated, not a stronger coupling.
The present integral-source construction is a distinct
arithmetic example, but still not a coloring obstruction.

### A rotation-invariant displacement screen

For one connected component with at least one edge, let D be
its set of actual (oriented) complex unit directions and let
S₅=R+iR for the coefficient ring R in the mod-5 lemma.
A global Euclidean rotation places all of D in S₅ if and
only if, for one reference edge direction z₀∈D,

    z·conj(z₀) ∈ S₅    for every z∈D.

Indeed, multiplying two rotated directions, one conjugated,
cancels the common rotation; S₅ is closed under conjugation
and multiplication. Conversely rotation by conj(z₀) does
the job. In that case translate the rotated component
by a vertex and apply the mod-5 five-coloring.
An isolated vertex needs no edge direction. The criterion is
componentwise: components may use different rotations.

A globally rotated integral anchor star cannot beat this
screen. The 24-point control itself does beat the screen:
the connected middle patch contains the native lattice
step ρ between the actual sites ρx and ρ(x+1),
which is coefficient-integral with integral inverse.
It also contains either exact cross displacement with
pole order one, in the same component. Multiplying by
conj(ρ) cannot restore integrality, since ρ is integral.
Thus no single rotation puts all of this component's
unit directions in S₅. The explicit five-coloring above
still works, so clearing even this invariant screen
is only a necessary condition for this approach.

### Reproduction

```sh
mkdir -p overlay-tmp
export TMPDIR="$PWD/overlay-tmp"
export PYTHONDONTWRITEBYTECODE=1
(ulimit -v 132000; timeout 70s python3 replay.py \
  ../three-copy-finite-stress/fixture.py \
  ../three-copy-saturation-150/replay.py NEW_OUTPUT)
cmp NEW_OUTPUT/samples.json verified/samples.json
cmp NEW_OUTPUT/exact-24.json verified/exact-24.json
cmp NEW_OUTPUT/saturation-44.json verified/saturation-44.json
cmp NEW_OUTPUT/summary.json verified/summary.json
```

The replay pins both sibling checker source hashes.
One guarded run completed in 0.301 s. No solver, Lean,
Git, or broader search was run.

Independent invariant-screen regression, using the published graph:

    PYTHONDONTWRITEBYTECODE=1 python3 check_rotation_screen.py ../three-copy-finite-stress/fixture.py verified/exact-24.json

The receipt identifies two actual unit edges in the same connected
component whose direction quotient is nonintegral at 5.
