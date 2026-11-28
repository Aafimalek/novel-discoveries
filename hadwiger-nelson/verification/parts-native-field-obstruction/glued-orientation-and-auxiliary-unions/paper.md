---
title: "Five-Colorings of Glued Triangular Lattices with Auxiliary Sites"
author:
- "Aafi Khan Malek"
date: "November 2026"
geometry: margin=1in
fontsize: 11pt
mainfont: "DejaVu Serif"
monofont: "DejaVu Sans Mono"
colorlinks: true
---
 
Independent Researcher, Ahmedabad, India · <aafimalek2032@gmail.com>.  
This research note was developed with AI assistance.
 
This is a handwritten infinite structural obstruction for the
[81-site fixture](https://github.com/Aafimalek/novel-discoveries/tree/a27775bee5782ed20476b0bec59d28be5031ccde/hadwiger-nelson/verification/parts-native-field-obstruction/exterior-cross-fixture-81), not for
all Parts-type coordinate sets.

Let `s=√−3`, `ω=(1+s)/2`, `Λ=Z[ω]`,
`K=Q(s,√33)`, and `J=Q(√−11)⊂K` where √−11=s√33/3.
Let `ρ=(7+√−15)/8`, the exterior rotation used by
[Parts, arXiv:2010.12665v2, §§2,4](https://arxiv.org/html/2010.12665v2#S4).
In particular |ρ|=1 and Re(ρ)=7/8.

For any set Γ of norm-one elements of J, put
`B(Γ)={0} ∪ ⋃_{γ∈Γ} γΛ`, where γ and −γ represent the
same lattice. Allow arbitrary Γ, including infinite sets,
and take independent Γ_A and Γ_B. Define

    U = B(Γ_A) ∪ ρ B(Γ_B).

**Theorem.** The induced unit-distance graph on U admits a
proper five-coloring. For any chosen distance-two pair in U,
it has a proper five-coloring making those two colors equal.
The latter assertion is pointwise in the chosen pair, not a
single palette that simultaneously makes every such pair equal.

The 81-site fixture is contained in this set for
`Γ_A={1,σ,τ}` and `Γ_B={1,σ}`, where
`σ=(5+√−11)/6` and `τ=(49+3√−11)/50`. The theorem includes
doubling all three full lattices under ρ, or arbitrary further
norm-one J orientations on either side.

## Classification of cross distances

The square classes of -3,33,-15 are independent, using primes 11
and 5 and then the sign of -3. In particular j=√−15 is not in K
and ρ∉K. Thus the two sides of U share only zero.

For x∈B(Γ_A) and y∈B(Γ_B), expand the squared cross distance as

    |x−ρy|² = N(x)+N(y) − (7/4)Re(x·conj(y))
              + (j/8)(x·conj(y)−y·conj(x)),

where N(x)=|x|². The terms besides the last lie in K and the
coefficient of j lies in K. Hence a rational squared distance
forces x·conj(y)=y·conj(x). If both x and y are nonzero, they
are parallel, in the sense of lying on the same real line
through the origin, with either sign allowed.

Parallel nonzero lattice sites must come from the same
orientation up to sign. To see this, suppose they come from
γΛ and δΛ, so their quotient has the form f g with
f=γ/δ=a+b√−11∈J and g=c+d s∈Q(s) nonzero. If f is not ±1,
then b≠0 (a real norm-one element of J is ±1), and a≠0
(the equation 11b²=1 has no rational b). The imaginary part
of f g has independent terms a d√3 and b c√11. It cannot
vanish unless c=d=0. This contradiction proves the claim.

For one orientation write x=γap, y=γbp with p∈Λ and a,b∈Z.
Such a lattice direction p exists because two real-parallel
Eisenstein points have rational quotient: the quotient belongs
to Q(s) and its real subfield is Q. One can take p primitive
in the two integer coordinates, so all points on that rational
line are integral multiples of p. The exact norm identity is

    16|x−ρy|² = N(p) [(a+b)² + 15(a−b)²],

with positive integer N(p).

* At squared distance one the right side is 16. If a≠b,
  then |a−b|=1, N(p)=1 and |a+b|=1, forcing one endpoint
  zero. If a=b, then N(p)a²=4: the cross edge joins the
  same native point x=y on the radius-two shell. Edges
  involving zero already belong to one of the two sides.
* At squared distance four the right side is 64. If a=b,
  N(p)a²=16 and both endpoint radii are four. If |a−b|=1,
  |a+b| must be one of 1,3,5,7; the corresponding values
  of (a+b)²+15 are 16,24,40,64. Only 16 and 64 divide 64.
  The first again has a zero endpoint; the last gives one
  radius three and one radius four, with N(p)=1. If
  |a−b|=2 then N(p)=1 and |a+b|=2, again a zero endpoint.
  Larger differences are impossible.

Thus genuinely cross-side unit edges are exactly the matching
radius-two references where both matching points are present.
A genuinely cross-side distance-two pair has radii (4,4),
(4,3), or (3,4).

## The shell is independent

In each triangular lattice γΛ, the radius-two shell is
2γ times the six norm-one Eisenstein units. Indeed N(v)=4
implies v∈2Λ because Λ/2Λ is the field F₄, conjugation descends
to an automorphism of that field, and the image of v·conj(v)
is zero. Then v/2 has norm one. Solving
N(m+nω)=m²+mn+n²=1 gives the six units stated.
Two distinct shell points in the same orientation are at
least two apart, because their directions are multiples
of 60 degrees.

For shell points in distinct orientations, a unit distance
would require Re(f w)=7/8, where f=a+b√−11 is their norm-one
orientation ratio and w is a sixth root of unity. If w is
nonreal, its imaginary part is ±√3/2, and this expression
contains a nonzero irrational term ±b√33/2 in addition to
a rational number. If w=±1, it would require a=±7/8, hence
11b²=15/64. This has no rational solution: the right side
has odd 5-adic valuation whereas 11b² has even 5-adic
valuation. Thus each side's entire radius-two shell is
independent.

## Explicit coloring, with optional terminal equality

Use the [native 2-adic four-coloring](https://github.com/Aafimalek/novel-discoveries/tree/b2f2d863aa4903b8aee52efc006e26f3c8b738b8/hadwiger-nelson/verification/parts-native-field-obstruction)
of the unit-distance graph on all of K, and copy it onto
the exterior side via inverse rotation. Both agree on zero.
Before recoloring, every unit edge inside each side is proper.
Recolor the entire radius-two shell on either one side
with a fresh fifth color. The shell is independent there,
and every genuine cross-side unit edge has exactly one
endpoint recolored. This gives a proper five-coloring,
also for infinite orientation sets.

For a chosen distance-two pair contained in one side,
recolor the *opposite* shell instead. In the side containing
the pair the native 2-adic coloring gives the two points
equal colors; there is no change at zero. For a genuinely
cross-side distance-two pair, select a radius-four endpoint
and recolor that endpoint's side's shell. The radius-four
point is not adjacent to its own radius-two shell by the
reverse triangle inequality. The other endpoint is
also not adjacent to that shell: genuine cross-side
unit edges have both endpoints at radius two, whereas the
other endpoint has radius three or four. Give the two
nonadjacent terminals the same fifth color as the shell.
No edge becomes monochromatic. This completes the proof.

## How to leave the obstruction

The theorem covers unions of individual triangular lattice
orientations, not their Minkowski sums, additive closures,
or arbitrary native-field points. In particular, actual
Parts-type auxiliary joins use different nonzero collinear
radii in opposite copies, which the theorem excludes within
the union family. The standard radii
√11/2±√3/6 have irrational ratio, while above any two
parallel nonzero sites in the native orientation union
have rational ratio. Thus the auxiliary join is a direct
algebraic way to escape the original incidence classification.
We now prove that this auxiliary family still admits five colors.

This written result is not formalized in Lean.

## Extension to the standard unequal-radius auxiliary sites

Write $r=\sqrt{33}$, $p=s(r+1)/6$, and $q=s(r-1)/6$.

In each native side, start with any union of norm-one J rotations
of full Λ (possibly infinite and independent between sides).
Also permit an arbitrary set of auxiliary sites of the form
γp or γq for any norm-one γ∈J, without requiring that their
orientation occur in the ordinary lattice union. Allow signs
independently (−γ is again norm one). Let A,B be the resulting
native sets, each including 0. Then the unit-distance graph on

    A ∪ ρB

admits a proper five-coloring. For any selected pair at distance
two anywhere in this union, there is a proper five-coloring
with that pair equal. This is pointwise in the choice of pair.

In particular take the earlier infinite glued fixture and
adjoin p,q to each native side, i.e. add p,q,ρp,ρq to the union.
This gives genuine unequal-radius cross-copy unit edges, but
does not escape the coloring obstruction.

### Exact cross-incidence classification

If x∈A and y∈B, the preceding expansion of |x−ρy|² shows that
any rational squared cross distance imposes x·conj(y)∈R,
since √−15∉K. Thus nonzero native representatives x,y must
lie on the same real line. The overlap between the two
sides is still only zero.

**One auxiliary and one full-lattice point.** Cancel the auxiliary
orientation, which leaves a full-lattice point of the form f z
with |f|=1 in J and z∈Λ. Since p and q are purely imaginary,
f z must also be purely imaginary. Write f=a+b√−11, z=c+d s,
with a,b,c,d rational. If f is not ±1, both a and b are nonzero
(there is no rational b with 11b²=1), and

    Re(f z) = ac − bd√33.

A zero real part then forces c=d=0 by irrationality of √33.
For a nonzero full-lattice point the orientation must therefore
be f=±1. Also Λ∩iR=Zs: in the lattice coordinates m+nω,
zero real part means 2m+n=0. Thus the possible native pair,
after dividing out the common rotation, is ks and
s(r±1)/6 for an integer k. Either order of the two points
gives the same squared cross norm. It equals

    3 [ k² + ((r±1)/6)² − (7/4)k(r±1)/6 ].

The coefficient of r is ±1/6−7k/8, which cannot vanish
for integer k. This also holds at k=0. Hence no such cross
pair has even a rational squared distance. In particular
there are no unit edges or distance-two pairs of this type.

**Two auxiliary representatives.** Their rays can be parallel
only if their relative orientation in J is real (the ratio
p/q is real), hence ±1. Fix one common orientation and keep
the possible signs explicitly. Then N(p)=(17+r)/6,
N(q)=(17−r)/6, N(p)+N(q)=17/3 and p·conj(q)=8/3. Matching
radial types p/p or q/q have squared cross norm equal to
N(p) or N(q) times 1/4 (same sign) or 15/4 (opposite signs);
these are irrational. Mixed p/q with opposite signs has
squared norm 17/3+14/3=31/3. Mixed p/q with the same sign
has squared norm 17/3−14/3=1. As a consequence the new
cross edges are exactly

    γp ↔ ργq   and   γq ↔ ργp

when the endpoints are present, with γ including the
common sign. There are no new cross distance-two pairs.

**Two full-lattice representatives.** The earlier classification
continues to apply: away from shared origin, cross unit
edges are matching radius-two references, with matching
native representatives, and any genuinely cross-side
distance-two pair has radii (4,4), (4,3) or (3,4).

### Coloring

Give each side the same [native 2-adic coloring](https://github.com/Aafimalek/novel-discoveries/tree/b2f2d863aa4903b8aee52efc006e26f3c8b738b8/hadwiger-nelson/verification/parts-native-field-obstruction)
after applying inverse rotation on the exterior side.
It is already proper on every edge internal to a side,
including any auxiliary vertex. Moreover, it distinguishes
each newly introduced mixed auxiliary edge across sides:
the difference of the two native representatives is
±γ(p−q)=±γs/3 of squared norm 1/3. Conjugation preserves
the normalized valuation used by the native coloring;
this norm has valuation zero, so the difference itself
has valuation zero. It lies in the integral coset and
its F₄ residue is nonzero, exactly the certificate for
different native colors. The two sides still agree at 0.

Neither auxiliary radius is two, so both radius-two shells
are the independent full-lattice shells proved earlier.
Recolor either of those shells with a fresh fifth color.
This fixes the matching reference edges without disturbing
any new auxiliary cross edge, proving proper five-colorability.

For two chosen distance-two points contained in one side,
recolor the other shell instead. The native coloring gives
equal colors to such a pair in K; this also covers pairs
involving the shared 0. For a genuinely cross-side pair at
distance two, the classification is unchanged. Recolor the
shell on a radius-four endpoint's side; this point cannot
neighbor its own shell (radial gap two), and the other
terminal cannot neighbor that shell across sides (only
the reference and auxiliary unit incidences above exist).
Give both terminals the fresh fifth color. They are not
neighbors of each other, so this is a valid equality witness.

This result uses only unions of single rotated lattices
plus the stated auxiliary radius types. It makes no claim
about adding arbitrary native points or Minkowski sums,
or about the published full five-chromatic Parts graphs.
These are written proofs; they have not been formalized in Lean.
