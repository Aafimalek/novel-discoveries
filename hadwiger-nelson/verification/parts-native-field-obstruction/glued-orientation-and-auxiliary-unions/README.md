# Parts-style gluing of any number of rotated triangular lattices

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
algebraic way to escape this specific obstruction, not a
proof of a non-five-colorable graph.

No numerical search, SAT, Lean, or Git was used to derive
this theorem.
