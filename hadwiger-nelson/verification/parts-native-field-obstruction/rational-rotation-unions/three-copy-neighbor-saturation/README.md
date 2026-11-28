# Exact upper-neighbor saturation beyond the 128-site fixture (not run)

Use the same three-copy set K ∪ ρK ∪ ρ²K as in the
[128-site fixture](https://github.com/Aafimalek/novel-discoveries/blob/baa6a6d60d52b036daeafb4424c787c8f1fc0817/hadwiger-nelson/verification/parts-native-field-obstruction/rational-rotation-unions/three-copy-finite-stress/README.md), where
K=Q(√−3,√33) and ρ=(31+3√−7)/32. Take the normalized valuation
of the embedding K into Q₂(η), where η²+η+1=0, √−3 maps to
1+2η, and the 2-adic root of 33 is the branch √33≡1 mod 4.
Its residue field is F₄, conjugation preserves the valuation,
and O is its valuation ring in K. This note gives necessary
conditions and a bounded proposed test, not a new ordinary
chromatic bound.

## Exact cross-neighbor constraints

For copy index difference k=1 or 2, set c_k=Re(ρ^k)∈Q and
h_k=4k. A cross unit edge between nonzero native representatives
x,y forces them collinear, by the
[two-copy squared-norm identity](https://github.com/Aafimalek/novel-discoveries/blob/0bf59bc95f82db5764382256922a9847191a2c1f/hadwiger-nelson/verification/parts-native-field-obstruction/rational-rotation-unions/README.md).
Thus y=t x with t∈F=Q(√33), and the exact unit equation is

    t²−2c_k t+1 = 1/N(x),       N(x)=x·conj(x).

Suppose the fixed representative x has negative valuation m.
If the quadratic has one root in F, its other root is in F as
well. Their sum 2c_k has valuation −h_k. The product
1−1/N(x) has valuation zero because v(1/N(x))=−2m>0.
The two roots must have distinct valuations h_k and −h_k:
equal valuations would both be zero and their sum could
not have negative valuation. The roots give exactly one
higher and one lower cross unit neighbor whenever they
exist. In particular each point has at most **one actual
higher unit neighbor per other copy**, not just one upper
residue label.

There is no unit triangle with one nonzero vertex from
each copy. Collinearity along its three cross edges would
make the three coordinates u t_i ρ^i for nonzero u∈K and
real t_i∈Q(√33). The ratio of two sides based at one vertex
would belong to Q(√33,√−7), but would have to equal
(1±√−3)/2 for an equilateral triangle. The independent
square classes of 33,−7,−3 rule this out. Thus a low
vertex's two higher attachments cannot themselves be
the endpoints of a unit edge. The common origin and a
unit point in each of two distinct copies cannot form
a triangle either: both native nonzero representatives
then have valuation zero, so the negative product
valuation dominates their cross squared norm.

## Structural filters for a finite six-critical subset

The integral locus is five-colorable by the complementary-shell
argument in the [128-site note](https://github.com/Aafimalek/novel-discoveries/blob/baa6a6d60d52b036daeafb4424c787c8f1fc0817/hadwiger-nelson/verification/parts-native-field-obstruction/rational-rotation-unions/three-copy-finite-stress/README.md).
Hence any finite inclusion-minimal non-five-colorable graph
would have a negative minimum valuation m. A vertex in a
native O-coset at that lowest valuation has at most two
cross edges, since they must go to higher valuations and
there are two other copies. Native edges stay in the
same O-coset. Minimality implies minimum total degree at
least five (otherwise a five-coloring of the deletion
extends greedily). Consequently:

* Every vertex in the lowest coset has native degree at
  least three in that coset. A native degree-three vertex
  must have actual higher unit neighbors in both other copies.
* Every connected component of a lowest coset must fail
  3-choosability. Otherwise remove it, five-color the
  remainder, and list-color the component: each vertex
  still has at least three available colors after
  excluding its higher neighbors' colors. In particular
  it cannot be connected and cubic by the list Brooks
  bound (a unit graph has no K₄).
* Each such component must contain a vertex of total
  degree at least six. If all total degrees were five,
  the available lists after coloring the deletion would
  have sizes at least the native degrees. A unit graph
  has no K₄: the two common unit neighbors of a unit
  edge are separated by √3. A Gallai tree in a unit
  graph can therefore have only clique blocks of order
  at most three or odd cycles. A leaf block supplies a
  noncut vertex of degree at most two, inconsistent
  with minimum native degree three. Thus the component
  is degree-choosable and its lists extend the coloring,
  a contradiction.

### Published list-coloring input

P. Erdős, A. L. Rubin, and H. Taylor,
[*Choosability in graphs*](https://www.renyi.hu/~p_erdos/1980-07.pdf),
*Congressus Numerantium* 26 (1980), pp. 125–157.
The characterization is on printed p. 141 (their D-choosability
and non-D terminology); p. 144 states the list version
of Brooks' bound. The characterization was independently
obtained by O. V. Borodin. This is an external finite graph
theorem, separate from the local field and geometry above.

### Two anchors that already fail double attachment

Let S=449/256. The two low anchors of the 128-site fixture
were S and S+1 in copy 0. Neither is double-attached even
in the infinite ambient set. The extreme-copy attachment
of S already exists. Its adjacent-copy discriminant is

    c₁²−1+1/N(S) = 54408001/(32·449)².

The numerator is strictly between 7376² and 7377² and
is prime to 3. This number is neither a rational square
nor 33 times one, so it has no square root in F.
For S+1=705/256 the adjacent-copy attachment exists.
Its extreme-copy discriminant is

    c₂²−1+1/N(S+1) = 65536/497025 − 60543/262144 < 0.

So it has no extreme-copy neighbor. The existing four-cycle
uses distinct lower anchors for its two upper colors;
this is not just a missing edge of the finite recipe.

## One bounded finite next test

Retain the exact 128-site fixture. Define W and the native
Moser spindle M as in that recipe. Set P=(W+W)∪M, a 22-site
native patch: the 19-point lattice ball plus the three
rotated spindle-only sites. It contains native 4-chromatic
structure and native degree above three. Put this patch
at S+P in copy 0 (valuation −8) and 31/16+P in copy 1
(valuation −4). The previous smaller negative blocks are
included in these patches.

For each member of each patch, adjoin **every** actual
higher unit neighbor in each other copy by the exact
quadratic above. This is one upward pass only, with no
recursion on new points. At most two points per patch
member can be added. Before deduplication the upper
bound is 128+44+88=260 sites. Preserve the positive
shell joins of the original fixture.

1. For native x and destination j let D=c_k²−1+1/N(x).
   Represent it as a+b√33 with rational a,b. If b=0,
   try rational square roots of a and a/33. Otherwise
   find the rational square root z of a²−33b², if
   any, try both signs in u²=(a±z)/2, and set v=b/(2u)
   for each nonzero rational root u. Verify every
   candidate u+v√33 by exact squaring. Each rational
   test takes integer square roots of numerator and
   positive denominator. This is exhaustive by comparing
   the coefficients of (u+v√33)².
2. Among t=c_k±√D choose exactly the one of valuation
   h_k if roots exist. For exact valuations, lift the
   2-adic root of 33 with branch 1 mod 4 (a square
   congruence mod 2^(n+1) determines that branch mod
   2^n). The two possible valuations are h_k and −h_k,
   so sufficient binary precision is finite. For native
   coordinates in the 1,η basis the valuation is the
   minimum of the two coefficient valuations. Check
   that the proposed point ρ^j(t x) has squared
   distance one from ρ^i x by exact norm evaluation.
3. Deduplicate canonical rational coordinates in the
   bitmask basis with generator squares (−3,33,−7);
   audit every one of the at most 33,670 unordered
   squared distances with the two independent norm
   formulas from the prior fixture. Count vertices
   with two actual higher neighbors separately by
   coset and native degree.
4. Before any solver, peel vertices of total degree at
   most four and store the deletion order. If the
   5-core is empty, replay the reverse greedy order
   as a full positive five-color witness and stop.
   Otherwise report the exact core, its lowest cosets,
   native min/max degrees, double attachments and any
   subcubic lowest components. The structural filters
   may delete specific candidate critical components,
   but alone do not color a general nonempty core.

Stop honestly if saturation yields no new active bridge
or the entire graph peels. The ≤260-site candidate has
not been generated or tested. No numeric search, Lean,
or SAT was run for this note.
