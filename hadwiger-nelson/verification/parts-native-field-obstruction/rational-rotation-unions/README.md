# A family of exterior rotations with a five-color obstruction

Let `K=Q(√33,√−3)⊂C`. Let ρ be any unit rotation not in K
whose real part c lies in Q, and set λ=2(1−c).
Assume that `v₂(λ)=−h<0` for an integer h>0.

**Theorem.** The induced unit-distance graph on

    K ∪ ρK

admits a proper five-coloring. For the integral locus defined
below, any one selected distance-two pair can also share a
color in a proper five-coloring of that integral locus.

This generalizes the
[specific Parts rotation proof](../hn-parts-full-field-gluing/README.md):
ρ=(7+√−15)/8 has λ=1/4 and h=2. There is no assertion
here about more than two copies or about distance-two equality
on all of K∪ρK.

## Local setup

Fix either embedding of √33 into Q₂ (33≡1 mod 8), and embed
K into Q₂(ω), where ω²+ω+1=0 and √−3↦1+2ω. The valuation v
has v(2)=1, v(0)=+∞. The extension has residue field F₄,
and its involution ω↦−1−ω acts as ordinary conjugation on K.
Thus `v(N(x))=2v(x)` for N(x)=x·conj(x).
Let O be the set of elements of K with valuation ≥0.
Its residue field is all F₄ because (√−3−1)/2 maps to ω.
Color O by its native residue: a unit difference has
valuation zero and hence a nonzero residue. Native unit
edges any place in K stay within one additive O-coset,
joining distinct modulo-2O residues there. For native
distance-two differences the valuation is one.

The sides K and ρK meet only at zero since ρ∉K. For a
cross pair represented by x,y∈K, write η=ρ−c. By complex
conjugation, conj(η)=−η; because η∉K, 1 and η are
linearly independent over K. Expansion of the squared
distance yields

    |x−ρy|² = N(x)+N(y)
              − c(x·conj(y)+y·conj(x))
              + η(x·conj(y)−y·conj(x)).

If this squared distance is rational, its η coefficient
vanishes. Thus z=x·conj(y) is real and

    |x−ρy|² = N(x−y) + λz.

For nonzero representatives let a=v(x), b=v(y),
d=v(x−y). The two summands have valuations 2d and a+b−h.
If a≠b then d=min(a,b). If the summand valuations differ,
the valuation of their sum is the smaller.

## The integral coloring

First give both O and ρO their native residue colors, using
inverse rotation on the second side. These agree at zero.
If a cross unit edge with both representatives integral has
the same native color, then d≥1, so its first summand has
valuation at least two. The other summand must therefore
have valuation zero, and a+b=h. Neither a nor b is zero:
otherwise the valuations differ and their difference has
valuation zero. Thus both lie in the range 1,…,h−1.

Recolor every site of valuation 1 through h−1 on one chosen
side with a fresh fifth color. This is an independent set
because all these elements have positive valuation; zero
is not recolored. The recoloring fixes every cross unit
edge with equal original colors, which has exactly one
endpoint recolored, and cannot introduce a new cross
conflict. Unit edges involving zero were already handled
by the original residue coloring. The resulting color is
constant modulo 2O among any one fixed integral valuation
b on a fixed side, since the recoloring decision depends
only on b. When h=1 this shell is empty and the integral
coloring already uses four colors.

## Negative levels: a single forbidden upper color per coset

Suppose a cross unit edge has minimum valuation m<0.
Neither endpoint is zero, since a displacement from zero
with negative valuation has squared distance of negative
valuation. If a=b=m, then 2m−h is strictly smaller than
2d≥2m, so the squared distance cannot be one. Assign the
lower endpoint to x and the higher to y in the symmetric
simplified formula. Then 2d=2m<0, so cancellation to
valuation zero requires a+b−h=2m. The higher valuation
is consequently b=m+h.

For a nonzero edge pair the ratio t=y/x is real, hence
belongs to Q(√33) and embeds in Q₂. It satisfies

    N(x) f(t)=1,       f(X)=X²−TX+1,       T=2c=2−λ.

Here v(T)=−h, and `v(4/T²)=2+2h≥4`. Consequently
(1-4/T^2) is 1 modulo 8, and has a square root in Q₂.
Thus f splits in Q₂. Its two roots have valuations h and
−h: their product is one and their sum T has valuation
−h, so the root valuations cannot be equal, and the
smaller must be −h. Name the positive-valuation root r₊
and the other r₋. Since v(t)=h, we have v(t−r₋)=−h.
The factorization then gives

    v(t−r₊)=h−2m,        v(y−r₊x)=h−m≥2.

For two points x,x′ in the same negative O-coset on one
side, the approximations differ by
`v(r₊(x−x′))≥h≥1`. Thus all opposite-side upper
neighbors of that entire coset lie in one modulo-2O
residue of one opposite-side O-coset, and all have the
same valuation m+h.

Process the negative integer levels in order m=−1,−2,....
The integral coloring is the seed. At stage m each upper
neighbor has already been colored at level m+h. If that
level is negative, its color is constant on its residue
inside the coset by induction. If it is integral, the
fixed-valuation seed constancy applies. Therefore all
upper neighbors of a level-m coset use at most one color.
Assign its four residues four distinct colors excluding
that one if present. Native edges inside each coset are
proper; native edges between cosets do not exist; all
negative cross edges join distinct levels h apart, so
every cross edge is handled when its lower level is
colored. This proves the five-coloring.

An explicit deterministic choice does not require finding
actual upper unit neighbors: choose a fixed representative
x₀ of the current coset, approximate r₊ by a rational
r′ with `v(r′−r₊)≥h−m`, and use the already-known color
of y*=r′x₀ on the other side as the forbidden color.
Here v(y*)=m+h; for any actual upper neighbor y,
`v(y−y*)≥h≥1` by the two estimates above. The finite
fractional binary parts of the two coordinates in the
basis 1,ω give canonical representatives and rational
truncations, as in the specific Parts rotation proof.

## Optional integral distance-two equality

There is more flexibility in the integral recoloring:
for each a∈{1,…,h−1} independently, choose exactly one
of the two valuation levels (left a, right h−a) to
color fifth. Recoloring any union of positive levels
on the same side causes no native conflict. A cross unit
edge between two positive levels requires a+b=h since
its first summand has valuation ≥2. Thus painting one
of each complementary pair works, with no edge between
two painted levels. All potentially equal-colored cross
unit edges are covered.

For a chosen distance-two pair contained in one side,
paint all the bounded positive levels on the opposite
side; the marked native residues agree and remain so.
For a genuinely cross pair, both representatives are
nonzero; the valuation of squared distance is two.

* Both a=b=0 is impossible since the summand of
  valuation −h then dominates.
* If both a,b≥1, the squared distance requires
  a+b≥h+2: otherwise the summand of valuation a+b−h<2
  dominates the first, whose valuation is ≥2. Thus
  these marked levels are not complementary. For any
  marked level in the relevant range choose the other
  level in its complementary pair; the choices cannot
  conflict. Both terminals retain their common native
  residue zero.
* If one valuation is zero and the other positive, the
  first summand has valuation zero. To attain valuation
  two requires cancellation, and hence the positive
  valuation must be h. Paint only levels 1,…,h−1 on
  the positive terminal's side. The positive terminal
  cannot neighbor its own painted shell. The valuation
  zero endpoint cannot neighbor that shell across the
  sides because the other summand would have negative
  valuation and dominate. Give the two marked endpoints
  the same fifth color. They are nonadjacent, so this
  causes no conflict.

This proves pointwise equality on O∪ρO, not a single
coloring simultaneously equating every such pair.

## Comparison with the earlier field-square result

The [July 2026 working report for Erdős problem 508](https://www.erdosproblemaday.com/report/508)
proves five-colorability of the entire real coordinate
square over F=Q(√3,√5,√11). It covers, in particular,
the original Parts rotation K∪((7+√−15)/8)K.
The 2-adic proof here is a separate mechanism with
applications beyond that ambient coordinate square.
For example

    ρ = (31+3√−7)/32,       λ=1/16,       h=4

satisfies the hypotheses. Its imaginary coordinate
3√7/32 is outside F by independence of the rational
square classes of 3,5,7,11. Also ρ∉K since the square
classes of -3,33,-7 are independent. Thus this two-copy
family is not contained in the cited F². We do not
claim a five-coloring of the whole square over F(√7)
or of the whole field generated by K and ρ, nor a new
plane chromatic bound. No Lean, SAT, or Git was run.

The compiled note is in paper.pdf and its TeX is in paper.tex.
Replay the exact finite controls with `python3 color_general.py`.
The module uses only the Python standard library. It checks the
original and the new rotation; the infinite proof is not inferred
from those finite runs. The ordinary-residue coloring of the
optional terminal variant is a written result, not a Lean check.
