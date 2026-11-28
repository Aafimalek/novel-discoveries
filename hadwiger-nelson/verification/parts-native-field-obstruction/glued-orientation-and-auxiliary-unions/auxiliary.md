# The standard unequal-radius auxiliary pair still permits five colors

This is a written extension of the
[rotated-lattice union obstruction](README.md).
Use the notation s=√−3, r=√33, K=Q(s,r), J=Q(√−11)⊂K,
Λ=Z[(1+s)/2] and ρ=(7+√−15)/8. Let

    p = s(r+1)/6 = i(√11/2+√3/6),
    q = s(r−1)/6 = i(√11/2−√3/6).

These are the auxiliary radii described by
[Parts, arXiv:2010.12665v2, §4](https://arxiv.org/html/2010.12665v2#S4).
They escape the previous union family, but adding them alone
does not give a non-five-colorable coordinate set.

## Statement and exact scope

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

## Exact cross-incidence classification

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

## Coloring

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
No computational search, SAT, Lean or Git was used.
