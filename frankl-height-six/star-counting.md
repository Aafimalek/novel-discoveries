# Further restrictions on the height-six forcing graph

These are statements about a **ground-minimal weak counterexample**:
a finite, nonempty union-closed family of nonempty sets, with no chain
of seven members and no point in strictly more than half its members.
The earlier [forcing-star reduction](lean/FranklForcingFiber.lean)
shows that the proper-forcing graph consists of disjoint outward stars
and isolated points. A proper arrow $p\to s$ means every set containing
$p$ also contains $s$, with $p\ne s$. All frequencies below are
for the original sets unless explicitly projected.

## An isolated point is necessary

[FranklProjection.lean](lean/FranklProjection.lean) checks that **every
ground-minimal weak counterexample has an isolated point**. Suppose not,
and intersect each member with the set of all leaves.

* No member becomes empty: a point is either a leaf, or is a center
  that forces a leaf. The image is union-closed. If seven image members
  formed a strict chain, incrementally unioning their original
  witnesses would lift it to a strict chain of seven original members.
* Fix a leaf $s$. Projection is injective on members missing $s$.
  Its own center is absent from those members. The existing local
  twinning theorem makes every other center's membership equal to that
  of any one of its leaves. Therefore the projected leaf set determines
  the entire original member.
* Consequently the number of members missing $s$ is unchanged, while
  the number containing $s$ can only fall. The at-most-half constraint
  survives for all retained points. At least one center is removed,
  contradicting minimum ground size.

This argument includes the case of just one nontrivial star and uses
neither a parity assumption nor a claim about exact-half frequencies.

## Counting when there are at least two stars

Let $k\ge2$ be the number of nontrivial stars, $i$ the number of
isolated points, $\ell$ the number of leaves, $n=i+k+\ell$, and
$m=i+k-2$. Write $H(d)=1+d+\binom d2$.
[FranklStarCounting.lean](lean/FranklStarCounting.lean) checks
$$
\ell\le\binom m2,\qquad
n-1\le H(m-1)\quad\text{or}\quad
n-1+\binom{k-2}{2}\le H(m).
$$
Subtraction is natural-number subtraction in Lean.

For two leaves in different stars, the members avoiding both form a
union-closed fiber of at least $n-1$ members. The three ambient members
$U\setminus\{p,s\}\subsetneq U\setminus\{p\}\subsetneq U$ are all
strictly above every member of the fiber, where $p$ is the first
center and $s$ its selected leaf. The first strict extension uses the
second selected leaf. This bounds the fiber height by three. Local
twinning removes both selected stars entirely and allows each remaining
star to be replaced by one coordinate. Projection to these
representatives preserves cardinality, strict inclusions and unions.

[FranklHeightThreeSauer.lean](lean/FranklHeightThreeSauer.lean) bounds a
union-closed family of height at most three on $d$ coordinates by
$H(d)$. If it shattered three points, start with a witness for the
empty trace and successively union witnesses for the three singleton
traces. This produces four distinct members in a strict chain.
[Mathlib's Sauer–Shelah theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SetFamily/Shatter.html)
then bounds cardinality by the number of at-most-two-element subsets.
Combining the two counts gives $n-1\le H(m)$.

If $n-1>H(m-1)$, every pair fiber uses all $m$ available coordinates.
Its maximum is exactly the ground minus its two selected stars. Fix a
leaf from each of two stars. Apart from the full ground and the
$n-2$ distinct single-point avoidance maxima that contain both chosen
leaves, each pair of *other* stars supplies a distinct further member.
Such a member omits at least three points, whereas a single-point
avoidance maximum omits at most two. There are
$\binom{k-2}{2}$ more members containing both leaves in this way.
Since each leaf appears in at most half the original members, the
number avoiding both is at least the number containing both. This
gives the second branch of the displayed disjunction.

## A center with two leaves

[FranklMultiLeafPair.lean](lean/FranklMultiLeafPair.lean) checks the
stronger restriction $n\le 2+i+\binom{i}{2}$ whenever there are at
least two nontrivial stars and one center has two or more leaves.
In particular, there must be at least three isolated points.
With this center fixed, all its pair-fiber maxima are the same.
If two differed, taking their union would insert an additional member
strictly between one pair maximum and the largest set avoiding the
selected leaf. The inclusion is strict because the second leaf of the
fixed center is missing from both maxima but present in the
single-leaf avoidance maximum. The longer upper chain contradicts
the height-six bound with the original lower count. The common
maximum misses every nontrivial star, so only the $i$ isolated
coordinates can support that pair fiber. Apply the height-three bound
there.

## Reproduce

Compile the existing sibling `FranklForcingFiber.lean`, then the
new modules below in order. Use Lean 4.36.0 and Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. If running inside that
Mathlib checkout, arrange its pinned dependencies and cache, then
replace `/path/to/repo` with this checkout:

```sh
cd /path/to/mathlib
D=/path/to/repo/frankl-height-six/lean
M=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$D:$M"
for f in FranklForcingFiber FranklHeightThreeSauer FranklCrossStarPair \
         FranklPairExtra FranklHeightThreeArithmetic FranklStarIndex \
         FranklPairSaturation FranklStarCounting FranklSaturatedPartners \
         FranklMultiLeafPair FranklProjection; do
    lean --root="$D" -o "$D/$f.olean" "$D/$f.lean" || exit
done
```

The displayed axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry` or native
decision axiom is used. These restrictions do **not** establish the
general height-six statement: a hypothetical minimal counterexample
with isolated points remains possible under these results. No
priority claim is made.

### Stronger signature and degree-moment restriction

The [signature-moment continuation](verification/signature-moments) raises the written and exactly replayed one-isolate forcing-star bound from 14 to 30. Lean checks the new fiber inequality, but the numerical bound of 30 is not yet an end-to-end Lean theorem. The earlier fully Lean-checked numerical bound remains 14. This does not cover other isolate counts or solve height six.
