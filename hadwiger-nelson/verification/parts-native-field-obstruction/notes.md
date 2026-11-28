# Why the native field of Parts's {1,2} scaffold cannot yield a unit-only obstruction

Source: [Jaan Parts, arXiv:2010.12656v2, §3](https://arxiv.org/html/2010.12656v2#S3).
Parts obtains a 199-vertex two-distance graph from a 313-vertex
construction with allowed edges of lengths one and two, and reports
a pair at distance 5/√3 forced equal in any proper five-coloring under
those two forbidden distances. Two rotated copies give a finite
two-distance non-five-colorability witness. This is not a unit-only
non-five-colorability certificate.

## Exact structural obstruction

Let W consist of 0 and the sixth roots of unity. Parts uses
W ∪ αW ∪ α⁻¹W, where
α = exp((i/2) arccos(5/6)) = (√33 + √−3)/6,
with √−3 having positive imaginary part. This follows by the
positive half-angle formulas cos²=11/12 and sin²=1/12. Thus all
coordinates of the Minkowski sum, its radius-√3 cut, and any
subset chosen from the cut lie in K=Q(√33,√−3).

**Lemma.** There is a simultaneous four-coloring of the unit-distance
graph on all complex points of K in which the endpoints of every
distance-two pair share a color.

**Proof.** Since 33 is 1 modulo 8, it has a square root in Q₂.
One direct proof is to start with an odd root mod 8, then at
level m≥3 choose the root r or r+2^(m−1) to arrange the next
square congruence mod 2^(m+1): the two squares differ by 2^m
times an odd number at this precision. The resulting sequence
converges in Q₂. Embed K into Q₂(ω), where ω²+ω+1=0 and
√−3 maps to 1+2ω. Fix the chosen square root of 33. The
polynomial of ω is irreducible mod 2; the residue field of
R=Z₂[ω] is F₄. For an element a+bω, the local valuation is
min(v₂(a),v₂(b)): after division by its common power of 2 it
has nonzero image in F₄, and multiplication of normalized
units remains nonzero in that field. This also proves
multiplicativity of that valuation. The induced involution
ω↦−1−ω preserves R and its residue nonzeros, hence preserves
valuation. Under the embedding this involution is ordinary
complex conjugation on K, as it fixes √33 and negates √−3.

If d is an exact unit displacement in K, then d conjugate(d)=1,
so twice its local valuation is zero. Write O for elements of K that
map into R. Partition the additive group K into cosets of O, choose
a representative in each coset, and color a point by the F₄ residue
of its difference from its representative. There are no unit edges
between cosets, and any unit edge within a coset is nonzero mod 2,
so has different endpoint colors. If d has Euclidean length two,
then d/2 has unit length and valuation zero. Thus d has valuation
one, and its endpoints are in the same coset with equal residues.
This proves both assertions. ∎

For the finite scaffold no coset choices are necessary: the
basic wheel sites and rotations have valuation zero when nonzero,
so every Minkowski-sum site is integral and four-coloring is by
simple coordinate residue reduction. The lemma also covers all
enlargements that remain inside K (or an isometric copy of K).
In particular no distance-two terminal-difference gadget can
be found by deeper Minkowski sums, enlarging the cut, or adding
more sites while remaining in this field. The proof also applies
inside any isometric copy of K. More generally, a conjugation-stable
nonarchimedean place with residue field of size at most four yields
the same coset coloring, whether ramified or not; at residue
characteristic two its distance-two pairs share their color.

The bound four is sharp for K. Two unit diamonds with common
endpoint 0 can use far endpoints u=√−3 and v=ρ₀u, with
ρ₀=(5+√−11)/6∈K. Their middle vertices are (u±1)/2 and
ρ₀(u±1)/2. Both diamonds have two adjacent middle vertices
at unit distance from each endpoint. The seven points are
distinct: the middle vertices have radius one and the two
distinct far endpoints radius √3; the middle-vertex pair's
angular increment is 60 degrees and the rotation is strictly
between zero and 60 degrees. Their far endpoints satisfy
|u−v|²=3·(2−2·5/6)=1. A three-coloring gives the endpoints
of each diamond the same color (the two shared neighbor colors
are distinct), contradicting that last unit edge. This is the
ordinary Moser spindle, not a new lower bound.

### Joined scaffolds and precise source scope

The native field claim immediately applies to Parts's 199-vertex
half. It also applies, in a slightly larger field, to its
canonical two-copy gluing using a **unit chord**. The marked
radius has square 25/3, so the relative rotation has cosine
1−1/(2·25/3)=47/50, and multiplier
γ=(47+√−291)/50. Both copies, including rotation about a
marked terminal, lie in K′=Q(√33,√97,√−3), because 291=3·97.
As 97≡1 mod 8, both real square roots again lie in Q₂ and
conjugation acts on Q₂(ω) exactly as above. So the unit-only
graph on this joined realization is four-colorable too,
with every distance-two pair equal. In particular dropping
length-two restrictions cannot yield the desired lower bound.

Parts's separate [unit-distance minimization paper, arXiv:2010.12665v2,
§§2–3](https://arxiv.org/html/2010.12665v2#S2) uses base coordinates
(a+b√33+ic√3+id√11)/(4·3^h) in the very same K, but its
joined construction L∪ρS uses an exterior rotation
ρ=(7+√−15)/8. This is not the above unit-chord multiplier γ.
Indeed −15≡1 mod 8, so its square root splits at 2; conjugation
swaps the relevant embeddings, and the two valuations of ρ
are ±2 (the numerators sum to 14 and multiply to 64).
This calculation explains why the native-field obstruction
does not contradict Parts's published unit-only five-chromatic
joined graphs. It likewise says nothing about the global
non-five-colorability theorem.

## Precisely what would convert the two-distance proof

Let H be a finite algebraically embedded all-unit graph with
marked terminals u,v at distance two, such that every proper
five-coloring of H has different terminal colors. If H itself
is not five-colorable, it is already the desired obstruction.
Otherwise treat H as a non-vacuous difference gadget: for each
length-two edge a,b of the exact two-distance obstruction include
a copy of H via the complex affine isometry

    z ↦ a + (b−a)(z−u)/(v−u).

Retain the original unit edges and every copied unit edge. A
proper five-coloring would restrict to a proper {1,2}-coloring
of the scaffold, a contradiction. Incidental shared vertices
and further unit edges do not weaken this argument; no unit
edge collapses under an isometry. If only a smaller subset of
the length-two edges is logically necessary, replace only that
subset. This gives an explicit coordinate graph when H is supplied.
Its chromatic number is at least six; a vertex-minimal induced
non-five-colorable subgraph has chromatic number exactly six
because deleting one vertex leaves a five-coloring, then adding
it back needs at most one new color.

An independently sufficient target is a finite unit-only
forced-equality pair at distance r≥1/2. Two isometric copies
sharing the first terminal can put the other two terminals at
distance one by rotation (chord 1 on radius r), creating the
contradiction directly, without simulating Parts's other edges.
Parts's reported equality is conditional on length-two edges,
so does not supply this unit-only gadget. The distinct global
non-five-colorability result yields existence of some finite
obstruction by compactness, not a concrete H or a finite
coordinate list for this route.

## Small field-escape experiment, not run

One explicit way to break the above local obstruction is to
adjoin √−7 and the unit direction β=(3+√−7)/4. The equation
s²=−7 splits over Q₂ since −7≡1 mod 8, and ordinary complex
conjugation swaps the resulting embeddings rather than fixing
a chosen 2-adic place. More concretely the two 2-adic numbers
3+s and 3−s have product 16 and sum 6. The minimum of their
valuations is one: both valuations are positive since s is odd;
if both were ≥2, the sum would have valuation ≥2. Their
valuations are therefore 1 and 3; β has valuation −1 or +1.
This unit-edge direction is not compatible with the native-field
unit-valuation-zero coloring proof. Merely adjoining a radical
without breaking that proof need not help. Breaking it does
not imply a five-color obstruction.

Escaping 2-adic stability is not by itself enough. The smaller
field Q(√−3,√−7) (omitting the original α radical) has a
three-coloring by a conjugation-stable place above 3. In
Q₃(√−7) the discriminant is a nonsquare mod 3, so it is
unramified quadratic with residue F₉=F₃[i], i²=−1;
adjoining √−3 is Eisenstein over that local field, and
does not enlarge the residue field. Conjugation on the
residue field is i↦−i, so every residue of an exact unit
displacement a+bi has a²+b²=1. Exactly one of a,b is zero,
hence a+b≠0. Color by a+b in F₃ after subtracting an
integral-coset representative. This gives a proper coloring
of the entire smaller field, in fact with different colors
also at every distance-two pair, since multiplication by
2 does not annihilate a nonzero F₃ color difference. Thus
a fixture using only that field can neither yield a finite
unit-only non-five-colorable graph nor force distance-two
difference under all five-colorings: its distance-two colors
can be merged without violating unit edges by recoloring
one terminal with a fourth color and the other with the same
fourth color, because the two terminals do not form a unit
edge.

A bounded falsifiable independent pilot should therefore mix
the original α rotations and β. For example, set T=W+W
(the 19-point radius-two hexagonal lattice ball), and take
F=T+αW+βW, with at most 931 sites and marked terminals 0,2
already in T. Its coordinates are in
Q(√33,√−3,√−7). Exact rational arithmetic in a multiquadratic
basis suffices to deduplicate and generate the complete unit
edge set. The first proposed test would be a properly checked
explicit equality coloring of 0 and 2, which would reject this
fixture. Failure to find a coloring or a deadline proves nothing;
a checked refutation with equality imposed is needed to call it
a difference gadget. Also check ordinary five-colorability,
unless the fixture itself is certified not five-colorable.
This is a small field-mixing pilot, not a claim of success or
optimality. No numerical search, Lean, SAT, or Git action was
performed.
