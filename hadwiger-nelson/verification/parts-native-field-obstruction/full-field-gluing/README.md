# Five-coloring both full native fields under one Parts rotation

Let `K=Q(√33,√−3)⊂C` and `ρ=(7+√−15)/8`. This is the
exterior rotation in [Parts, arXiv:2010.12665v2, §§2–4](https://arxiv.org/html/2010.12665v2#S2).
Let `U=K ∪ ρK`.

**Theorem.** The entire unit-distance graph on U admits a
proper five-coloring. In particular no finite subset of this
double-field coordinate set is a six-chromatic witness. This
covers arbitrary collections of points in the two copies,
without assuming bounded denominators or 2-adic integrality.

The proof extends the
[integral theorem](integral-lemma.md).
We make no new assertion here about distance-two terminal
equality for cross pairs outside the integral locus, or about
three or more exterior copies.

## Local setup and the known integral part

Fix either 2-adic root of 33. Embed K in Q₂(ω), where
ω²+ω+1=0, by √−3↦1+2ω. For the normalized valuation v,
the conjugation of K preserves v, and v(N(x))=2v(x).
The ring R=Z₂[ω] has residue field F₄. Put O=K∩R in
this embedding; the residue of O is all F₄ because
(√−3−1)/2 maps to ω.

The square classes 33, -3, -15 are independent, so ρ∉K;
thus the two sides of U meet only at zero. On O∪ρO,
use the known integral five-coloring: give both sides
their native F₄-residue color, with inverse rotation
on the exterior side, and recolor the valuation-one
shell on just one side with the fifth color. This coloring
has the following property: among points on a fixed side
of fixed valuation b=0 or b=1, its color is constant in
each residue modulo 2O. Indeed, on each such set the
decision to recolor the shell is constant, and the native
color is the residue.

Native unit edges on either side have differences of
valuation zero. Consequently every such edge lies within
one additive O-coset of its side, and connects distinct
residue classes modulo 2O there. Each additive O-coset
has four such residue classes.

## Cross edges below the integral locus

For a cross unit edge the native representatives x,y are
collinear: the coefficient of √−15 in the exact squared
distance forces x·conj(y) to be real, as in the integral
theorem. If the lower endpoint has negative valuation,
neither endpoint can be zero: the squared length to zero
would have negative valuation. Write a=v(x), b=v(y);
for collinear representatives the cross squared norm is

    N(x−y) + x·conj(y)/4.

If a=b=m<0, the second summand has valuation 2m−2, strictly
below that of the first, contradicting square norm 1.
If the valuations differ, let a=m<0 denote the lower
one (we may exchange the native roles for this calculation).
The first summand has valuation 2m<0. Thus its valuation
must equal a+b−2 for cancellation to produce square norm 1.
It follows that b=m+2.

The ratio t=y/x is real, hence belongs to the real subfield
Q(√33) and embeds in Q₂. Symmetrically whichever copy holds
the lower endpoint, the squared norm identity is

    N(x) f(t)=1,       f(X)=X²−(7/4)X+1.

The roots of f in Q₂ are (7±s₂)/8 for a 2-adic square
root s₂ of -15, which exists since -15≡1 mod 8.
The two numerators are even, have sum 14 of valuation 1,
and product 64 of valuation 6. Therefore their valuations
are 1 and 5 and the root valuations are −2 and +2.
Call the root of valuation +2 r_lo and the other r_hi.

Here v(t)=b−a=2, so v(t−r_hi)=−2. Using the exact
factorization f(t)=(t−r_lo)(t−r_hi) and v(N(x))=2m gives

    v(t−r_lo)=2−2m,       v(y−r_lo x)=2−m≥3.

In particular, take any two points x,x′ in the same
negative-valuation O-coset (all its points have valuation
m), and any of their opposite-side upper neighbors
y,y′. Then v(r_lo(x−x′))≥2, and each actual neighbor differs
from its approximation by valuation at least 3. Hence
v(y−y′)≥2. Also all such upper neighbors have valuation
m+2. This proves that all upper neighbors of a fixed
lower coset lie in one residue modulo 2O in one
opposite-side coset. It is a classification of potential
upper-neighbor colors, not of all geometric edges.

## Coloring by descending level

Start with the integral coloring. Descend through the
integer levels m=−1,−2,−3,… on both sides. At stage m,
each opposite-side upper neighbor of a level-m coset
has already been colored at level m+2. If that level
is negative, its coloring is constant on each of its
four residue classes in the coset by induction. If
it is integral, its valuation is 0 or 1 and the
constancy property of the seed coloring applies.
Thus there is at most one color among all already-colored
cross neighbors of the coset we are processing.

Assign the four residues in this O-coset four distinct
colors, avoiding that one color if it is present.
This makes all unit edges inside the coset proper,
and every cross unit edge to the previously colored
upper level proper. Distinct cosets within a side
have no native unit edges. Cross edges with a negative
endpoint always join distinct levels two apart, so there
are no same-stage conflicts. Any cross edge to a lower
level will be handled at that lower stage. Every site
has an integer valuation or is zero, and therefore
all sites are covered. This proves the theorem. ∎

### Optional deterministic residue rule

There is no need to identify which geometric upper neighbors
exist to construct this coloring. For a coset C at level m,
take its canonical representative x₀ whose two coordinates
in the Q₂-basis 1,ω are finite fractional binary parts
(dyadic rationals in [0,1) representing the coordinates
modulo Z₂). The representative is in K because
ω=(√−3−1)/2 under the embedding. Choose the canonical
integer truncation r′ of r_lo modulo 2^(2−m), and put
y*=r′x₀∈K. Then v(y*)=m+2 since r′ has valuation 2.
For every possible upper neighbor y of any x∈C,

    v(y−y*) ≥ min(v(y−r_lo x), v(r_lo(x−x₀)),
                     v((r_lo−r′)x₀)) ≥ 2.

Thus y and y* are in the same already-colored residue
and have the same valuation, so use the color of y*
on the opposite side as the single forbidden color,
regardless of whether any actual upper neighbor exists.
Fix an order of the four residues and give them the
four remaining color labels in order. The rule requires
only finitely many recursive levels for each site and
agrees with the preceding proof of properness.

This is a handwritten proof about the particular two-copy
ambient coordinate set. It is compatible with known
five-chromatic graphs produced by this gluing and is not
a whole-plane chromatic bound. No numerical search,
SAT, Lean or Git was used.

The PDF also records sharpness from Parts's published 509-vertex type-M
graph, not a new finite lower-bound construction. See §§2, 4 and 6 of
<https://arxiv.org/html/2010.12665v2>. The proof uses ordinary graph
coloring, not an additive homomorphism. It gives no new planar bound.

Run `python3 color.py` for the deterministic exact-rational implementation
and its finite check (105 vertices and 87 unit edges, including nine
rational tests with negative valuation). The proof of all coordinates is
in paper.pdf / paper.tex; no Lean formalization is claimed.
