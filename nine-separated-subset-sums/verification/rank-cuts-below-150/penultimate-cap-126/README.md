# Below 150, the penultimate weight is at least 127

For nine sorted positive real weights with 1-separated subset sums,
**$149\le x_9<150$ implies $x_8\ge127$**. This is the direct cap
$t=126$ on $\lfloor x_8\rfloor$, so all smaller caps are included
without requiring any separate verification at those caps.
It does not raise the established lower bound on $x_9$ to 150.

The proof dependencies are the earlier forbidden length-149 band,
exact Harper cuts, and the general moment, deficit, and interval
matching implications in the [cap-119](../penultimate-cap-119/README.md),
[cap-120](../penultimate-cap-120/README.md) and [cap-124](../penultimate-cap-124/README.md)
packets, and the immediately preceding [cap-125](../penultimate-cap-125/README.md)
application. Only the cap-specific arithmetic changes.

## Cap-specific premises

The eight forced rank runs merge into starts 137 through 172,
giving full-sign slots $q=29,\ldots,64$. Each corresponding base
signed magnitude $\alpha_q=u_{a-q+1}$ lies in
$[149-2q,151-2q)$, with common counts
$64\le a\le74$ and $b=148-a$. Values before the run are
strictly below 21, and values after it are at least 93 by spacing.
The established +2 inequalities give
$u_a<207$, $u_{a+1}\ge278$, $u_b<321$, $u_{b+1}\ge391$.
For instance, use $\alpha_{29}\ge91$ and $M<150$ for
$u_a\le2M-\alpha_{29}-2<207$, and $M\ge149$ for
$u_{b+1}\ge2M+\alpha_{29}+2\ge391$.
The exact bin capacities are thus:

| Half-open range | Capacity |
|---|---:|
| [1,21) | $a-64$ |
| each [149−2q,151−2q), q=64 down to 29 | 1 |
| [93,207) | 28 |
| [278,321) | $148-2a$ |
| [391,10000) | $a-20$ |

The final endpoint is loose: even the sum of the coordinate caps
is 988. Omitted ranges are forbidden.

Put $y=(120,\ldots,127)$, $r_i=y_i-x_i$, and $R=\sum_i r_i$.
Each deficit is in [0,119]. The 36 required slots force at least
one unbalanced sign pair, because only 35 complementary pairs are
balanced. The smallest unbalanced cap-vector magnitude is 232.
If $R\le139$, every unbalanced magnitude remains at least 93,
but **every required slot has a strict upper endpoint at most 93**.
Therefore $R>139$; the replay uses the weaker $R\ge139$.

## Exact replay

    sha256sum -c SHA256SUMS
    python3 cap_rank_bins.py

1. Unit cells for $(r_1,r_2)$: 7,140 total, 0 direct moment-loss
   rejections, 1,122 tail-bound rejections, 220 slot-only matching
   rejections, 5,798 go to stage 2.
2. Splitting those cells by all 11 possible values of $a$ gives
   63,778 cell/count profiles. No profile is excluded by the separate
   loss/tail check alone; all 63,778 fail the all-sign capacity
   matching. There are no survivors.

The replay uses only exact integers and fractions, with outward
rounding and complete interval matching. No heavy solver or Lean
audit is needed to run it. The proof of the geometric implications
is handwritten. This result does not exclude any $x_8\ge127$.
