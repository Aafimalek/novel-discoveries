# Below 150, the penultimate weight is at least 121

Under the earlier rank-cut premises, 1-separated subset sums of nine sorted
positive real weights with $149\le x_9<150$ force **$x_8\ge121$**.
The companion [cap-119 packet](../penultimate-cap-119/README.md) excludes every
$x_8<120$ by exact arithmetic. This packet excludes the additional
shard $120\le x_8<121$. It does not exclude the full interval for $x_9$.

[Paper (PDF)](paper/penultimate-at-least-121.pdf) · [TeX](paper/penultimate-at-least-121.tex)

## From known ranks to a full set of capacity bins

Here $M=x_9$, the cap is $t=120$, and the two-deficit moment uses the
same notation as the cap-119 proof. The consecutive forced run is
$q=23,\ldots,64$. In particular each $\alpha_q$ is one unsigned base
eight-weight full sign value, at exact index $j_q=a-q+1$. The common
counts $a,b$ are as before, with $64\le a\le74$ and $b=148-a$.

The $u$-values before index $j_{64}$ are all strictly below 21,
because $\alpha_{64}<23$ and consecutive $u$ spacing is at least 2.
Values after $j_{23}$ are at least 105 because $\alpha_{23}\ge103$.
Thus exactly $a-64$ values are below 21, and one is in each
half-open interval $[149-2q,151-2q)$ for $q=64,63,\ldots,23$.

The previous packet uses a +2 lower sharpening of threshold ranks.
There is an upper sharpening too. The full nine magnitude
$M-\alpha_q$ cannot coincide with $|M-u_i|$ for $u_i$ near
$2M-\alpha_q$ (nor $M+\alpha_q$ near $2M+\alpha_q$); every
different full magnitude is at least 2 away from it. Therefore

    u[a]    ≤ 2M−alpha[q]−2
    u[a+1]  ≥ 2M−alpha[q]+2
    u[b]    ≤ 2M+alpha[q]−2
    u[b+1]  ≥ 2M+alpha[q]+2.

For the first upper bound, if $u_a\le M$, then it already satisfies
the bound because $M-\alpha_q=d_q\ge45$. Otherwise compare the
magnitudes $u_a-M$ and $M-\alpha_q$. The second upper bound is
analogous. No ties at the threshold are possible. With the extreme
$q$-values and $149\le M<150$ this gives $u_a<195$,
$u_{a+1}\ge278$, $u_b<321$, $u_{b+1}\ge403$.

Hence the allowed bins for all 128 complementary base sign pairs,
with exact capacities, are:

| Half-open range | Number of values |
|---|---:|
| [1,21) | $a-64$ |
| each [149−2q,151−2q), q=64 down to 23 | 1 |
| [105,195) | 22 |
| [278,321) | $148-2a$ |
| [403,1000) | $a-20$ |

The last upper endpoint 1000 is harmless, since all eight weights
are at most 121. Intervals omitted from this table are forbidden.
The zero-capacity possibility $a=b=74$ is supported.

## Exact two-stage proof

The 42 forced $\alpha$'s require at least seven unbalanced signs,
but slots 23 through 28 are the only ones whose strict upper bounds
exceed 93. The minimum unbalanced magnitude at the cap vector
$y=(114,\ldots,121)$ is 220. As each signed magnitude can move
by at most the total deficit $R$, this gives $R>127$, safely
relaxed to $R\ge127$ in replay.

1. Cover $r_1,r_2$ by integer unit boxes and bound remaining deficit
   by the moment loss, as in the cap-119 packet. Using the minimum
   moment across all $a$ gives 291 cells that have not yet been
   excluded by the 42-slot-only matching.
2. Split each of these cells into the 11 possible counts
   $a=64,\ldots,74$. Use its own moment bound, stronger deficit
   bound, and the finite bins above. This is 3,201 cell/count
   profiles. Loss/tail bounds reject 2,498, and exact interval
   matching rejects every one of the other 703.

For the strengthened total-deficit bound in step 2, all $r_i\le113$.
The coarse bound is at most $D/114<226$ (where $D$ is the profile's
moment loss budget). If $R>113$, the inequality
$\sum r_i^2\le113^2+(R-113)^2$ follows by concentrating the
remaining mass, or by the same largest-entry argument as in the
cap-119 proof. Thus $2\cdot114 R-\sum r_i^2$ gives a monotone
lower bound on loss and yields the integer cutoffs in replay.
If the resulting $R$ is at most $220-23$, then $\alpha_{64}<23$
requires a balanced sign and the separate 39-bound R refinement
from the cap-119 proof also applies. None of these steps presumes
its relaxation is attainable.

For each profile use the outward-rounded rational interval of
possible magnitudes for each sign pair. In the ordered list of 128
unit-capacity positions obtained by expanding the bins, the positions
intersecting that interval are consecutive. Run earliest-deadline
matching against all 128 positions; the same exchange argument
as in the cap-119 proof proves greedy completeness even for repeated
bin boundaries. If there is a true weight vector, each sign pair
would map to a distinct position, so failure proves exclusion.

## Replay

    sha256sum -c SHA256SUMS
    python3 cap_moment.py
    python3 cap119_box.py
    python3 cap120_bins.py

The replay uses only standard Python and exact integers/fractions.
The implications are handwritten, and no Lean audit or full
nine-weight optimum claim is made.
