# Exact three-copy stress fixture, at most 128 sites

This is a static candidate, **not** a six-chromatic witness.
It has genuine unit joins at both offsets 4 and 8 and a
small obstruction to one natural restricted coloring rule.
Ordinary five-colorability of the exact 128-site candidate is
confirmed by a checked positive witness (see the replay below).

Let s=√−3, r=√33, K=Q(s,r), and write
ω=(1+s)/2 for the complex sixth root of unity. Take

    ρ = (31+3√−7)/32,
    σ = (5+√−11)/6 = (5+sr/3)/6,
    T = ρ+ρ⁻¹ = 31/16,
    S = ρ²+ρ⁻² = 449/256 = T²−2.

The three copies are K,ρK,ρ²K. Normalize a point in copy i by
dividing its complex coordinate by ρ^i. All normalized
valuations below are at the same fixed 2-adic embedding of K
into the unramified quadratic extension of Q₂, so the local
residue is F₄; O is its native integral subring. A **cell**
in one copy is one additive translate of 2O in the native
coordinate. The preceding
[many-copy bound](../multiple-copies/README.md)
gives ordinary chromatic number at most six for the entire
ambient coordinate family. The exterior coordinate √7 is
outside the real field F=Q(√3,√5,√11) of the
[July working report](https://www.erdosproblemaday.com/report/508).

## Coupling the three copies below the integral seed

On copy 0 put x=S+1 and x′=S, both of valuation −8
in the same additive O-coset. On copy 1 put y=ρT
(native valuation −4), and on copy 2 z=ρ² (native
valuation zero). Exact identities give a unit cycle:

    x−y   = ρ⁻²,
    y−z   = 1,
    x′−z  = ρ⁻²,
    x−x′  = 1.

Thus an earlier-level neighbor on each of the other copies
exists for the same level −8 coset. These two higher neighbors
are adjacent, so unlike the two-copy induction, they cannot
generally contribute just one color. This four-cycle alone
is not a high-chromatic graph.

## Four explicit bridge cells at each offset

The following rational operations make four unit edges across
each of the two offsets, one incident to every residue cell
of the same lower O-coset. For offset k=1 use A=S+1,B=T;
for offset k=2 use A=S,B=1. Then |A−ρ^k B|=1 and
v(A)=−8. Put

    c = Re(ρ^k),   D=1−c²,
    a₀=1/A,       t₀=B/A,
    u₀=a₀+t₀−c.

For each ξ∈{0,1,ω,1+ω}, write −ξ/A²=δ+b s with rational
δ,b, and form

    u = u₀+δ,
    v_real = (D−3b²)/u,
    a = (u+v_real)/2,
    t = c+(u−v_real)/2,
    X = 1/(a+b s),
    Y = t X.

Adjoin X on copy 0 and ρ^kY on copy k. Nonzero denominators
and the exact distance are verified as follows. If h=4k then
v(c)=−h−1 and v(t₀)=h. Both δ and b have valuation at least
15 since A has valuation −8 and coefficients of ξ in the
basis 1,s have denominators at most two. Hence u has
valuation −h−1 and is nonzero. At ξ=0 the construction
returns exactly A,B: the original unit identity implies
(a₀²-(t₀-c)²=D), so (v_{mathrm{real},0}=a₀-t₀+c).
The general identity

    a² − (t−c)² = u v_real = D−3b²

gives N(a+b s)=t²−2ct+1. Indeed N(a+b s)=a²+3b².
Since Y=tX with real t, this proves |X−ρ^kY|=1 once the
reciprocal is defined.

The exact error is

    a−a₀−δ = −[δ(δ+2a₀)+3b²]/(2u).

Here v(a₀)=8, v(2u)=−h and the numerator has valuation
at least 24, so the error has valuation at least 24+h.
Therefore Z=a+b s agrees to that precision with
(Z_* = a₀−ξ/A²); both have valuation 8.
The reciprocal (1/Z_*=A+ξ+ξ²/(A−ξ)) agrees with A+ξ
modulo 2O: its last term has valuation at least 8.
Also (1/Z) and (1/Z_*) differ by valuation at least
(24+h-16=8+h). Thus X lies in the cell of A+ξ.
In the four ξ choices these cells exhaust the four
distinct residues of the level −8 O-coset. The two
offsets concern the same four cells as A changes by 1.

By the [two-copy upper-neighbor estimate](../hn-rational-rotation-gluing/README.md),
each Y for k=1 lies in the native cell of T, since
the matching original edge (X,Y)=(S+1,T) came from the same
lower coset. Each Y for k=2 lies in the native cell of 1,
for the same reason using (S,1). In both cases the
native upper valuation is −8+h, as needed.

### Consequence for a restricted coloring rule

Put the translated native wheel S+W on copy 0, with
W={0}∪{ω^j:0≤j<6}. In its quotient by native cells,
the center has residue zero and the six rim sites
cycle around the three nonzero residues twice.
Spokes and rim edges produce every pair of the
four distinct residue labels: the quotient is K₄.

Suppose a proper coloring of the finite fixture is constant
on each native cell on each copy. Then the four lower cells
of the wheel must receive four distinct colors. Every one
of these cells has an edge to the cell of T on copy 1
and to the cell of 1 on copy 2, by the two constructions.
The latter cells have distinct colors since y and z are
adjacent. Therefore the four lower cell colors avoid two
distinct colors, requiring at least six total. This is
an exact obstruction to **cell-constant five-coloring**,
not to unrestricted five-coloring. In fact only the four
specified cells on copy 0 and one specified cell on
each of the other copies are needed for the obstruction.

## Positive shell edges and finite coordinate recipe

The adjacent rotation ratios have λ=1/16 and h=4;
the extreme ratio ρ² has λ=63/256 and h=8.
Thus 4↔4ρ↔4ρ² are two exact unit edges (native valuation 2).
Put

    p = 16/[3(2+s)],       U=(2−s)/(2+s).

Here N(p)=256/63 and v(p)=4, since N(2+s)=7 is odd.
Therefore p↔ρ²p is an exact unit edge across h=8.
To connect p to ordinary native sites by a short path,
use the 12 successive unit displacements obtained by
repeating twice the six-step list

    σ, σU, conj(σ), conj(σ)U, −1, −U.

Their sum is
(2(sigma+mathrm{conj}(sigma)-1)(1+U)
=2(2/3),4/(2+s)=p).
Every direction has norm one.

For concreteness the candidate is exactly the union of
the following sets, deduplicated as complex points:

1. On each of copies i=0,1,2 include the native core
   ((W+W)cup{3,4}cup D_0), where (D_0=Wcup M)
   and M is the seven-vertex Moser spindle with common
   endpoint 0, far endpoints s,σs, and middle sites
   ((s±1)/2, sigma(s±1)/2). The native core has at
   most 24 sites. All three copies share zero.
2. On copy 0 include S+D₀, and on copy 1 include T+D₀.
   Here D₀ has 11 sites. These are translated wheels and
   spindle diamonds, with native edges in the relevant
   negative cosets.
3. On copies 0 and 2 include all partial sums of the
   displayed 12-step path to p. Zero was already included.
4. Include each of the eight bridge pairs constructed in
   the previous section. For ξ=0, all four endpoints
   already occur in items 1 and 2, so this adds at most
   twelve further sites.

The bound is (3·24-2+2·11+2·12+12=128).
All actual induced unit edges should be used in a future
check, not just the explicit edges listed above.

## Why an integral-only enlargement cannot help here

For this particular triple, the entire integral locus
(Ocup
ho Ocup
ho²O) is five-colorable.
Start with the four common native residue colors on each
side. A cross unit edge with initially equal colors has
positive native endpoint valuations a,b satisfying
a+b=h for that pair of copies. More generally a cross
unit edge between positive valuations requires this sum,
even without first assuming equal colors, by the valuation
of the two summands of its squared norm.

Use the fifth color for middle-copy valuations 1,2,3, for
outer-copy valuations 5,6,7 on both outer sides, and for
valuation 4 on one outer side only. For each adjacent
copy ratio (h=4) the middle chosen levels cover exactly
one endpoint, and no colored outer-level site qualifies
as its opposite partner. For the outer ratio (h=8) the
complementary positive level pairs are likewise covered
exactly once. Within a copy all positive levels are
independent. Thus this is a proper seed with five colors.
The nonintegral stress module is needed to escape this
particular argument, not merely a second set of shell edges.

## Exact light replay

* Represent coordinates by exact rational coefficients in
  the bitmask basis with squared generators -3,33,-7.
  Their rational square classes are independent (use primes
  11 and 7, then the sign), so canonical coefficient rows
  identify points exactly. For (1/(a+b s)) use
  ((a-b s)/(a²+3b²)).
* Generate the explicit native rows and rotate by powers
  of ρ, deduplicate, and audit all at most 8,128 unordered
  pairs by exact squared norm. Use two independent formulas:
  generic radical multiplication with conjugation, and a
  real/imaginary split over (Q(sqrt{33},sqrt{21})).
  Check that the named spindle, bridges, and shell edges
  actually occur in the result.
* Only one bounded ordinary five-color query was made,
  with no residue-equality constraints. The complete model
  was replayed on all induced edges, after independently
  recomputing the exact graph by the real/imaginary norm.
  It splits every one of the six prescribed cells.

The exact graph contains 128 distinct sites, 8,128 complete
unordered pair checks, and 229 induced unit edges. One
Kissat 4.0.4 process returned SAT in 0.004 s. Generation
took 1.108 s and independent model verification 0.557 s.
The ordinary chromatic number is therefore at most five
(and at least four by the embedded spindle). No four-color
query was run. The finite restricted lower bound and the
integral/infinite family statements elsewhere in this note
are distinct from that claim. In particular, this finite
negative result does not settle the infinite three-copy
family. No Lean or Git ran.

Replay from this directory using a local `TMPDIR`:

```sh
mkdir -p overlay-tmp
export TMPDIR="$PWD/overlay-tmp"
(ulimit -v 150000; timeout 5s python3 fixture.py generate NEW_DIRECTORY)
cmp NEW_DIRECTORY/exact-graph.json verified/exact-graph.json
cmp NEW_DIRECTORY/ordinary-five.cnf verified/ordinary-five.cnf
# Existing certificate replay does not require a solver.
(ulimit -v 150000; timeout 5s python3 fixture.py check NEW_DIRECTORY solver.out)
cmp NEW_DIRECTORY/checked-positive.json verified/checked-positive.json
```

The original single solver invocation was separately
guarded with `timeout 12s` under the same 150,000 KiB
address-space cap. All tracked receipts are hashed.

