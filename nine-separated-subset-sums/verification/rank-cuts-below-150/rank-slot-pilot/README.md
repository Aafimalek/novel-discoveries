# Prescribed full-sign rank slots below 150

This is a **partial chamber search**, not an exclusion of [149,150).
The premises are the written [nine-weight rank cuts](../README.md)
and [central gap restrictions](../central-gap-restrictions.md). Let
(s_r) be the ordered nine-weight subset sums, normalized with ranks
1 through 512, and let (M=x_9=149+δ), (0≤δ<1). The other eight
weights retain their sorted indices 1 through 8.

## From prescribed cube edges to signed rank slots

The forced coordinate-9 starts in the lower representative window are

    k = 158, 159, 161, 162, 168, 169, 171, 172.

For such a k, rank k is a base subset A without coordinate 9; rank
k+148 is A together with that coordinate. Taking its complement yields
the base complement of A at rank 365-k. In particular both lower ranks
k and 365-k omit coordinate 9.

Fix the sign in coordinate 9 to plus when writing each of the 256
full signed forms (L_σ=M+∑_{i≤8}σ_i x_i), (σ∈\{-1,1\}^8).
Sort their absolute values, labelling them (d_1,ldots,d_{256}).
Because ranks r and 513-r are complements and all subset sums are
unit-separated, the (d_p) are distinct and
(d_p=s_{256+p}-s_{257-p}). For each forced k, the forms at positions
(p=257-k), (q=k-108) are (L_σ,L_{-σ}) in some order and are
both positive, because their upper complementary subsets contain
coordinate 9. Consequently their magnitudes sum to (2M).

The representative (q)-indices are

    q = 50, 51, 53, 54, 60, 61, 63, 64.

For each of them the two ranks defining (d_q) are in [172,320],
an interval of rank length 148 and real length M, with total gap
excess (1+δ). Unit spacing then gives
(2q-1≤d_q≤2q+δ<M). Thus the smaller form in the prescribed pair is
(M-α) for an oriented signed eight-weight form (α=∑_{i≤8}σ_i x_i>0),
and satisfies the exact linear rank-slot constraints

    149 - 2q ≤ α ≤ M - (2q - 1).

The larger form at p is (M+α). The signs `σ` used in the
certificate represent positive `α`, not the coefficient vector of the
smaller (M-α) form.

Two more exact consequences, not used in the pilot:

* For each consecutive q-pair (50,51), (53,54), (60,61), (63,64), its
  two (α)'s are consecutive in the order of positive absolute base
  eight-weight full signs. Their difference is twice a central gap.
  That gap is at least 1 and strictly below 2, while all distinct base
  signed magnitudes are at least 2 apart (their corresponding
  complementary ranks move at least one step each).
* Let (u_1<cdots<u_{128}) list those positive base magnitudes and
  (N(t)=\#\{i:u_i<t\}). For a forced (α=u_j), the 256 original
  magnitudes are (M+u_i) and (|M-u_i|); no thresholds relevant to
  these rank counts can tie, by full unit separation. The smaller
  rank is (q=1+N(2M-α)-j), the larger is (p=j+N(2M+α)). Their
  sum is 149, so (N(2M-α)+N(2M+α)=148).

## Auxiliary central root rows

The geometric reductions above are independent of these root cuts.
The pilot includes the earlier full-sign central orientation (ε),
(g=ε·x), (1≤g<2). If each of (d) disjoint pairs joins
opposite signs of (ε), replace the two weights in each pair by
their positive difference. Together with the unchanged weights
this gives (k'=9-d) unit-separated weights. As usual the embedding
adds the sum of the lower pair members to each signed configuration's
ordinary subset sums. Both original central complementary subsets
choose exactly one weight in every pair, so they are images of
complementary reduced subsets, and their difference is the reduced
configuration's central gap (g). The reduced total, letting (P)
be the indices of lower pair members, therefore satisfies

    ∑ x_i − 2 ∑_{i∈P} x_i ≥ 2^k' − 2 + g.

If there is exactly one weight with negative central sign in the
reduced configuration, a further improvement is valid. Write (T)
for the sum of the positive-side weights; (g=T-y_-). All
positive-side weights are at least (g+1): flipping just that sign
in the central relation gives a different complementary pair, whose
absolute difference is at least (g+2), and positivity selects the
positive partial-sum band. As there are at least two positive-side
weights in this application, the first and last gaps of their
subset-sum list are distinct and each is at least (g+1). Thus
(T≥2^{k'-1}-1+2g) and

    ∑ x_i − 2 ∑_{i∈P} x_i = 2T−g ≥ 2^k' − 2 + 3g.

Each retained inequality is generated from a concrete injective
matching; its ratio of signs and disjointness are checked with
integer assertions. In the reduced central orientation a pair keeps
the sign of its larger weight. For a fixed (d), componentwise
dominance of lower-index choices, with no smaller coefficient of
(g), preserves the stronger inequality.

## Pilot and exact scope

Only two central orientations and two slots were tested. Each row
takes the 256 oriented base sign vectors in lexicographic order:

| Central sign ε | Slot q | Exact exclusions | Choices not excluded |
|---|---:|---:|---:|
| `++++-+---` | 50 | 214 | 42 |
| `++++-+---` | 64 | 200 | 56 |
| `-------++` | 50 | 170 | 86 |
| `-------++` | 64 | 178 | 78 |

Each excluded choice has exact rational nonnegative Farkas
multipliers with (A^Ty=0). Usually (b^Ty<0). Four of the certificates
instead have (b^Ty=0) with positive weight on an original strict
row (M<150) or (g<2); their linear combination also proves
a strict contradiction. No rational-feasibility or chamber-validity
claim is made for the unexcluded choices. Counts for the two slots
are independent, not counts of compatible pairs.

The original root rejects 294 of 512 central orientations with exact
certificates. The matching inequalities (806 distinct nondominated
rows over the 218 root survivors; 916 when including the
singleton-negative refinement) give **zero additional full-orientation exclusions**.
A different bounded lookahead with at most five propagated comparisons
per root and eight attempted comparisons per step, branching on
(D_S≤-1) versus (D_S≥g+1), also gives none. All 218 original
central orientations remain unresolved. These are root measurements,
not a benchmark of full chamber search.

## Replay

```sh
./replay.sh
sha256sum -c SHA256SUMS
```

Replay requires only standard Python 3 and uses exact fractions;
SciPy/HiGHS was used to propose certificates, not to verify them.
To regenerate one pilot, invoke the corresponding Python file without
`--verify-only` (for `central_root_lp.py`, also give its JSON path).
There is no external engine, Lean check, or publication claim for
the geometric premises in this packet. The baseline source and
certificate are included unchanged for an independent replay.
