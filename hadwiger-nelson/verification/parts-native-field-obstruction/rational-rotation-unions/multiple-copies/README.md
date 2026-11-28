# Multiple exterior rotations: a (k+3)-color upper bound

Let `K=Q(√33,√−3)⊂C`, and let ρ₁,…,ρₖ be any finite list
of unit complex rotations with k≥1. Assume that each distinct
pair has ratio

    Rᵢⱼ = ρⱼ/ρᵢ ∉ K,
    cᵢⱼ = Re(Rᵢⱼ) ∈ Q,
    v₂(2(1−cᵢⱼ)) = −hᵢⱼ < 0.

The hᵢⱼ are positive integers; they need not coincide.

**Theorem.** The induced unit-distance graph on

    U = ⋃ᵢ ρᵢ K

has a proper coloring with k+3 colors. This also bounds the
chromatic number of every finite subset of U. There is no
terminal-equality claim in this theorem.

## Proof

Use the same 2-adic embedding as in the
[two-copy theorem](../hn-rational-rotation-gluing/README.md):
embed K into Q₂(ω) for ω²+ω+1=0, fix either 2-adic root
of 33, and let O be the intersection with the valuation
ring. Ordinary conjugation preserves the normalized
valuation v, so `v(N(x))=2v(x)`. The residue field of O
is F₄. Distinct copies intersect only at shared zero
because Rᵢⱼ∉K. Regard each nonzero point in a copy by its
native representative under inverse rotation.

For a particular cross edge from copies i,j, rotate both
sides by ρᵢ⁻¹. The exact two-copy arguments apply with
c=cᵢⱼ, λ=2(1−c) and h=hᵢⱼ. In detail, rational squared
distance forces x·conj(y) real, by independence over K
of 1 and the imaginary part Rᵢⱼ−c. The squared norm is
then `N(x−y)+λx·conj(y)`. For nonzero native representatives
of valuations a,b, the two summand valuations are
`2v(x−y)` and `a+b−h`.

**Integral seed.** Use the same four F₄ residue colors on
all k integral copies ρᵢO. If an integral cross unit edge
has equal residue colors, then v(x−y)≥1, so the other
summand must have valuation zero: a+b=h. Both a,b
are positive, since otherwise the two valuations
would be different and the difference x−y would
have valuation zero. Recolor all nonzero sites of
positive native valuation in k−1 of the copies,
using a distinct extra color for each such copy; keep
common zero unchanged. The painted sites are independent
within any one copy since they have differences of
positive valuation. A cross unit edge whose colors were
equal has at least one painted endpoint; if both are
painted they belong to different copies and their extra
colors differ. Any other edge remains proper. All unit
edges from zero were already proper and no positive
valuation site is its unit neighbor. This is a proper
integral seed using k+3 colors. On each copy it is
constant on any fixed-valuation residue modulo 2O.

**Negative levels.** For any cross-edge relation with a
negative endpoint, its two valuations cannot be equal:
then the product summand at valuation 2a−h would
strictly dominate. If the lower valuation is m<0,
the first summand has valuation 2m and must cancel
against the second. Hence the upper valuation is m+h.

For a fixed lower O-coset in copy i, consider its possible
upper neighbors in just one other copy j. The same
2-adic quadratic estimate as in the two-copy proof applies
using h=hᵢⱼ. Namely the ratio t=y/x lies in Q(√33), hence Q₂,
and is a root-approximation to the valuation-h root r₊ of

    f(X)=X²−2cX+1.

The roots in Q₂ have valuations h and −h (normalize
the discriminant by (2c)² to obtain a unit 1 mod 8).
Because `N(x)f(t)=1` and v(t)=h, one has
`v(y−r₊x)=h−m`. Replacing x by any other member x′
of the same O-coset changes r₊x by valuation at least h≥1.
Thus all upper neighbors in copy j of the lower coset
lie in the same modulo-2O residue at their common
valuation m+hᵢⱼ. This conclusion holds separately
for each j.

Now process m=−1,−2,… in descending valuation order,
on all copies. The upper neighbors have all been
colored, as hᵢⱼ>0. If their level is integral, its
color is constant in the indicated residue at the
given valuation by the seed property. If it is
negative, the recursion assigns a single color to
each of the four residue classes in a coset, so
again all such neighbors in j use at most one color.
Thus a lower coset has at most k−1 forbidden colors
among all previously colored neighbors. At least
four colors remain from a palette of k+3; assign four
distinct ones to its residue classes. Native edges
stay inside a coset and have distinct residues,
and every cross edge with a negative endpoint is
proper at the stage for its lower valuation. There
are no cross edges at equal negative levels to check
within a stage. Every point is eventually covered. ∎

## Explicit three-copy test family

Take

    ρ = (31+3√−7)/32,
    ρ² = (449+93√−7)/512,
    U₃ = K ∪ ρK ∪ ρ²K.

The two rotations are unit complex numbers. Both are
exterior to K, because √−7 does not lie in K (the
rational square classes -3,33,-7 are independent).
The three unordered rotation ratios, up to inverse,
are ρ, ρ, ρ². For ρ,

    2(1−Re ρ)=1/16,            h=4;

for ρ²,

    2(1−Re ρ²)=63/256,         h=8.

Thus the theorem proves `χ(U₃)≤6`. It proves neither
a lower bound of six for U₃ nor five-colorability of
U₃. Any actual six-chromatic finite witness here would
require a separate exact coordinate construction and
certified refutation of its five-colorability.

This is outside the square over
`F=Q(√3,√5,√11)` whose five-colorability was obtained in
the [July 2026 working report for Erdős #508](https://www.erdosproblemaday.com/report/508):
the point ρ has imaginary coordinate 3√7/32, outside F.
This only separates ambient coordinate sets. It does
not show any new lower bound, any full-field-square
coloring, or any bound for the whole plane.

More generally the powers 1,ρ,…,ρ^(k−1) satisfy the
hypotheses for any finite k. In Q₂ the two roots
(31±3√−7)/32 of the rotation polynomial have valuations
±4. The m-th powers likewise have valuations ±4m, so
the trace 2Re(ρ^m) has valuation −4m and the value of
h for a power difference m is 4m. If a nonzero power
were real it would be ±1 and could not have those
2-adic valuations, so each such power has nonzero
√−7 coefficient and stays exterior to K.

No numerical search, SAT, Lean, or Git was used.
