# Exact 150-site three-copy saturation: a checked five-coloring

The one-pass upper-neighbor test for the
[128-site three-copy graph](../three-copy-finite-stress/README.md)
is complete. Independent replay rebuilds the pinned original
128-point graph and its 229 unit edges. It exactly checks both
other copies for every point of each of the two translated
22-point native patches (88 tests). The four actual higher
attachments, in native coordinates, are:

| source copy | source | destination copy | destination |
|---|---:|---|---:|
| 0 | 449/256 | 2 | 1 |
| 0 | 705/256 | 1 | 31/16 |
| 1 | 31/16 | 0 | 1 |
| 1 | 31/16 | 2 | 1 |

All four destinations already belong to the starting graph.
Only the source 31/16 in copy 1 has both higher attachments.
The 22 new points are patch points. For the 150-site result
we exactly recomputed all 11,175 unordered squared distances
using two norm formulas. The induced graph has 285 unit
edges, all verified against a direct five-coloring, with
class sizes 27, 29, 36, 29, 29. No SAT or Lean was run; this
is an exact five-color upper bound on this finite test, not
a statement about the chromatic number of the infinite family.

## Correctly scoped mod-5 displacement lemma

Put R=Z_(5)[√3,√7,√11], with Z_(5) the rationals of denominator
prime to 5. The three rational square classes 3,7,11 are
independent. Thus the eight monomials with exponents 0 or 1
are an independent rational basis, and R is exactly the set
of elements whose coefficients in this basis are 5-integral.
As T²=3 is irreducible over F₅, send

    √3 ↦ T,    √7 ↦ T/3,    √11 ↦ 1

to the field F₅[T]/(T²−3), reducing coefficients modulo 5.
These images square to 3,7,11 respectively. The canonical
basis and multiplication by the quadratic relations show
this defines a ring homomorphism; no field homomorphism or
injectivity is asserted.

In that quotient write the two coordinate images as X=a+bT,
Y=c+dT, and set L(X,Y)=a+c+2d∈F₅. If X²+Y²=1 then L does
not vanish. Indeed, if L=0 then c=−a−2d, and the coefficient
of T gives a(b−d)=2d². If a=0 this forces c=d=0, and the
constant coefficient requires b²=2, impossible. Otherwise
put z=d/a. Then b/a=z+2z² and c/a=−1−2z. Dividing the constant
coefficient by a² gives

    a⁻² = 1+(1+2z)²+3(z+2z²)²+3z².

For z=0,1,2,3,4 the right side is 2,0,3,0,3, none a nonzero
square in F₅. This proves the finite quotient implication.
The replay separately enumerates its 24 unit directions
and checks all of them.

Therefore **any finite unit-distance graph for which every
actual unit displacement has both real coordinates in R**
is five-colorable. Translate each connected component by
one of its points; every other point in the component is a
sum of unit displacements, so lies in the translated R².
Apply the quotient color L there. This is a condition on
edges and their displacements, not on the original absolute
point coordinates. For a graph in Q(√3,√7,√11)² to escape
this five-color criterion, some actual unit displacement
must have a reduced denominator divisible by 5 in at least
one basis coefficient.

For this 150-site graph, every original coordinate has
5-integral coefficients, a stronger condition than needed.
The replay verifies this for each exact basis row and confirms
properness against all 285 unit edges. In the complex bitmask
basis with square generators (−3,33,−7), a coefficient row
q₀,…,q₇ maps to the tuple

    (a,b,c,d) = (q₀−q₅, q₂−q₇, 3q₃+q₆, q₁+q₄/3) mod 5.

Here the real and imaginary coordinates are reduced separately,
not the complex value via a map taking i to a chosen root
of −1.

## What the filter does not show; cancellation at 5

The exact unit displacement

    (-49 + √33 √−3)/50

has norm (2401+99)/2500=1 and a coefficient denominator
divisible by 5. It already lives in the native field K.
Thus the filter can genuinely fail even in a field with
a separate four-coloring. Failure is not evidence of needing
six colors, and this unit vector is not a cross attachment
in the tested graph.

Let F=Q(√33) be the real native subfield, s=√−3, and use a
place above 5. Both 33 and −3 are nonsquares modulo 5, so
their 5-adic radicals generate the **same** unramified
quadratic extension E of Q₅. Indeed the quotient
33/[4(−3)]=−11/4 is congruent to 1 mod 5 and has a unit
square root by Hensel. Choose the compatible branch
√33≡2s modulo 5 in E. Conjugation of K switches the two
local factors, rather than preserving the valuation in
one specified factor. For x=A+B s with A,B in F,
the valuation of N(x) is the sum of the valuations of
A+B s and A−B s in E. It is not generally twice
the minimum valuation of the chosen rational basis
coefficients, nor twice the valuation of one factor.

The exact counterexample is

    x=(√33−2s)²=21−4√33 s,       N(x)=2025.

Both displayed F coefficients are 5-units, but N(x) has
valuation 2. At the chosen branch the two local factors
of x have valuations 2 and 0: √33−2s vanishes modulo 5,
its conjugate does not, and their norm 45 has valuation 1.
This example shows why a norm-valuation cancellation test
cannot be replaced by a coefficient divisibility test.
It is **not** a claim that x yields an exact cross edge.

More precisely, for a coefficient-integral source x and
a cross ratio t∈F satisfying

    t²−2c t+1 = 1/N(x)

with c rational and 5-integral, a root is integral if
v₅(N(x))=0, by comparing the valuations of the three
terms in the corresponding monic quadratic. If v₅(N(x))>0,
a root necessarily has negative valuation and
2v₅(t)=−v₅(N(x)); in particular the positive norm valuation
must be even. In the fixed 5-adic place of F, the element
A=a+b√33 is integral if and only if both rational
coefficients a,b are 5-integral, because √33 gives an
independent residue basis. Hence native y=t x preserves
coefficient integrality precisely when both F coefficients
A,B can absorb the scalar valuation v₅(t). If x lies
in Q(s) with integral rational coefficients and
v₅(N(x))=2e, then both its coefficients are divisible by
5^e (the binary norm over this unramified field is
anisotropic modulo 5), so such a root cannot break the
filter. Genuinely mixed K sources may behave differently.
For the present ρ, the rotation powers and their inverse
are coefficient-integral over R and preserve R²; this
ensures that a true violation by t x could not simply be
removed by rotating the destination back into this ring.
No search for such a source was run.

## Reproduction

From this directory:

```sh
mkdir -p overlay-tmp
export TMPDIR="$PWD/overlay-tmp"
export PYTHONDONTWRITEBYTECODE=1
(ulimit -v 132000; timeout 90s python3 replay.py \
  ../three-copy-finite-stress/fixture.py \
  ../three-copy-finite-stress/verified/exact-graph.json NEW_OUTPUT)
cmp NEW_OUTPUT/exact-150.json verified/exact-150.json
cmp NEW_OUTPUT/saturation-88.json verified/saturation-88.json
cmp NEW_OUTPUT/mod5-unit-directions.json verified/mod5-unit-directions.json
cmp NEW_OUTPUT/summary.json verified/summary.json
```

The standard-library replay pins the original source and exact
coordinate graph, independently reconstructs the two patches,
checks exact quadratic roots in Q(√33) and their 2-adic
valuations, re-creates the full geometry, and validates the
direct mod-5 witness. The one guarded run took 3.792 s.
