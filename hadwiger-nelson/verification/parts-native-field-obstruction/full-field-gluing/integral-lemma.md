# Five-coloring the entire integral native locus with one Parts rotation

Let `K=Q(√33,√−3)⊂C` and `ρ=(7+√−15)/8`. Fix either root of
33 in Q₂ and the corresponding embedding of K in Q₂(ω), where
ω²+ω+1=0 and √−3 maps to 1+2ω. Let v be the normalized local
valuation (v(2)=1, v(0)=+∞) for this embedding. Put

    O = {x∈K : v(x)≥0},        U = O ∪ ρO.

**Theorem.** The induced unit-distance graph on U admits a proper
five-coloring. Any specified distance-two pair in U can be made
equal by a proper five-coloring, with the choice of coloring
allowed to depend on the marked pair. The theorem holds for
either choice of the 2-adic root of 33.

This strictly extends the earlier
[rotated-lattice union](../hn-parts-cross-unions/README.md) and
[specified auxiliary-pair](../hn-parts-auxiliary-unions/README.md)
results: integral native sites do not have to lie on any of
those rays, and integral finite Minkowski sums are covered.

## Native arithmetic

The 2-adic root of 33 exists because 33≡1 mod 8. The local
quadratic extension Q₂(ω) is unramified: x²+x+1 is irreducible
mod 2 and the residue of Z₂[ω] is F₄. Explicitly,
v(a+bω)=min(v₂(a),v₂(b)), because division by the largest
common power of 2 gives a nonzero image in that field.
The involution ω↦−1−ω preserves the valuation, and on K
is usual complex conjugation (it fixes the embedded real
√33, negates √−3). For N(x)=x·conj(x) this gives

    v(N(x)) = 2v(x).

In particular a native unit edge always changes the residue
in F₄, while a native distance-two displacement has valuation
1 and preserves it. Thus color O by its residue in F₄. These
facts are also detailed in the
[native field note](https://github.com/Aafimalek/novel-discoveries/tree/b2f2d863aa4903b8aee52efc006e26f3c8b738b8/hadwiger-nelson/verification/parts-native-field-obstruction).

Define the shell `S={x∈O : v(x)=1}`. This is an arithmetic
shell, not a Euclidean circle. It is an independent set for
unit edges: the difference of any two of its points has
valuation at least one, whereas a unit displacement has
valuation zero. In fact any native point of valuation at
least one cannot be a unit neighbor of a shell point.

## Cross valuations

The square classes of 33, -3, -15 are independent (use
primes 11 and 5, then the sign), hence j=√−15∉K and ρ∉K.
The two sides O and ρO intersect only at zero.

For x,y∈O, direct expansion gives

    |x−ρy|² = N(x)+N(y) − (7/4)Re(x·conj(y))
              + (j/8)(x·conj(y)−y·conj(x)).

If the squared distance is rational, independence of 1,j
over K forces z=x·conj(y) real. For this situation the
formula simplifies to

    |x−ρy|² = N(x−y)+z/4.

Take both representatives nonzero and let a=v(x), b=v(y),
c=v(x−y). Since a,b≥0, c≥min(a,b); moreover c=min(a,b)
if a≠b. The two summands in the simplified formula have
valuations respectively 2c and a+b−2. The first may be
+∞ if x=y. When these valuations differ, the valuation
of the sum is the smaller one.

Two consequences for cross unit edges (target valuation 0):

1. If the native residues of x and y coincide, then c≥1.
   The first summand has valuation at least 2. For the
   sum to have valuation 0, the second must have valuation
   0. Hence a+b=2, and a≠b would imply c=min(a,b)=0.
   Therefore a=b=1.
2. Any cross unit edge with a valuation-one endpoint must
   have both endpoints valuation one. If a=1,b=0, the
   summand valuations are 0 and −1, giving −1. If a=1,b≥2,
   they are 2 and b−1≥1, so their sum has valuation at
   least 1. Neither is unit. If y=0 instead, the squared
   distance has valuation 2a=2 and again is not unit.
   The same argument applies with the roles reversed.

For cross distance-two pairs (squared distance 4, target valuation
2), both a=b=0 is impossible: the valuation −2 of the second
summand is strictly smaller than the first. Both a=b=1 is also
impossible: the second then has valuation 0 while the first is
at least 2. All claims here are implications of exact arithmetic;
we do not assert these valuation tests characterize all
Euclidean unit or distance-two pairs.

## Five colors and equality of any chosen pair

Initially give both O and ρO the native residue coloring,
using inverse rotation on ρO. These agree at zero and are
proper on all edges contained within a side. Recolor S or
ρS, on just one side, with a fifth color. Every cross edge
that originally had matching colors has both endpoints in
the two shells, by consequence 1, so exactly one is now
recolored. No internal edge is spoiled by recoloring an
independent shell, and a cross edge cannot have both
endpoints with the fresh color. Edges involving zero were
already covered on one side. This proves proper five-coloring.

If the chosen distance-two pair is contained in one side,
recolor the opposite shell: its two native representatives
have the same residue and neither is recolored. This includes
pairs involving the common point zero.

For a genuinely cross-side distance-two pair with nonzero
representatives, at least one valuation is ≥1 and not both
are 1, by the cross steps above. Select an endpoint of
valuation ≥1 whose opposite endpoint does not have valuation
1: if exactly one endpoint has valuation 1 select that
one; otherwise choose any endpoint of valuation ≥1. Recolor
the shell on the selected endpoint's side. That endpoint
cannot neighbor its own shell by the native valuation
bound, and the opposite endpoint cannot neighbor that shell
by consequence 2. Now give both marked endpoints the fresh
fifth color. They are not neighbors of each other, so the
coloring remains proper.

## Scope

Every element of K of complex norm one belongs to O, and
O is closed under sums. In particular the native hexagonal
wheel and any of its rotations by such elements, and their
finite Minkowski sums, lie in O. This includes the standard
native wheel construction using the half-angle rotation
(√33+√−3)/6; it includes the native auxiliary representatives
s(√33±1)/6, since v(s)=0 and √33 is an odd 2-adic unit. It
does not cover arbitrary divisions by powers of 2, general
K∪ρK, or multiple exterior rotations.

For example the formal Parts coordinate type
(a+b√33+ic√3+id√11)/(4·3^h) with a−b+c+d≡0 mod 4
does not alone imply membership in O: (-1+√−3)/(4·3^h)
meets that congruence for every h but has valuation −1
since (-1+√−3)/2 is a norm-one direction. The theorem
does not classify the coordinates of the full published
five-chromatic Parts graphs. The source of the exterior
rotation is [Parts, arXiv:2010.12665v2, §§2–4](https://arxiv.org/html/2010.12665v2#S2).
No computational search, Lean, SAT, or Git was used.
