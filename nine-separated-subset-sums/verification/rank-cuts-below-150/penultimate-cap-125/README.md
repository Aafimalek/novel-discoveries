# Below 150, the penultimate weight is at least 126

For nine sorted positive real weights with 1-separated subset sums,
**$149\le x_9<150$ implies $x_8\ge126$**. This is the direct cap
$t=125$ on $\lfloor x_8\rfloor$, not a conclusion about the largest
weight reaching 150. No other cap replays are prerequisites. The
proof uses the prior forbidden length-149 band, exact Harper cuts,
and the general moment, deficit, and interval-matching arguments
in the [cap-119](../penultimate-cap-119/README.md), [cap-120](../penultimate-cap-120/README.md)
and [cap-124](../penultimate-cap-124/README.md) packets.

[Paper (PDF)](paper/penultimate-at-least-126.pdf) · [TeX](paper/penultimate-at-least-126.tex)

## Cap-specific premises and numerical replay

The eight forced rank runs merge into starts 136 through 172. In
full-sign rank terms, $q=28,\ldots,64$. Each signed base magnitude
$\alpha_q=u_{a-q+1}$ lies in $[149-2q,151-2q)$, with common counts
$64\le a\le74$ and $b=148-a$. Entries before this run are strictly
below 21, and entries after it are at least 95, by spacing at least
2. The established +2 threshold inequalities at the extreme q's
give $u_a<205$, $u_{a+1}\ge278$, $u_b<321$, $u_{b+1}\ge393$.
For example $\alpha_{28}\ge93$ and $M<150$ imply
$u_a\le 2M-\alpha_{28}-2<205$, and $M\ge149$ implies
$u_{b+1}\ge 2M+\alpha_{28}+2\ge393$.
Thus the bins and their exact capacities are

| Half-open range | Capacity |
|---|---:|
| [1,21) | $a-64$ |
| each [149−2q,151−2q), q=64 down to 28 | 1 |
| [95,205) | 27 |
| [278,321) | $148-2a$ |
| [393,10000) | $a-20$ |

The final endpoint is loose: the sum of the coordinate caps is
only 980. Any absolute full sign value not in a listed bin is impossible.

Let $y=(119,\ldots,126)$, $r_i=y_i-x_i$, and $R=\sum r_i$.
Each $r_i$ is between 0 and 118, inclusive. The 37 linearly ordered
required slots include at least two unbalanced complementary
sign pairs, since only 35 are balanced. The smallest unbalanced
cap-vector magnitude is 230. If $R\le137$, every unbalanced
magnitude remains at least 93, but only q=28 can reach 93
(the upper bound at q=29 is strict). Thus $R>137$; the replay
safely relaxes this to $R\ge137$. The exact loss bound from
the cap-124 packet applies with the deficit cap 118.

* Stage 1 covers 7,021 unit cells for $(r_1,r_2)$. Moment loss
  alone removes none; tail bounds remove 1,090, the slot-only
  matching removes 336, and 5,595 go to stage 2.
* Stage 2 covers 61,545 cell/count profiles after splitting by
  $a=64,\ldots,74$. None are removed by the profile loss/tail
  check alone, and **all 61,545** fail full interval matching
  with the capacity bins above.

The code is the same outward-rounded interval method as cap 124,
with the new cap and bins. It uses no floating arithmetic or
third-party solver. The finite check is not formalized in Lean.
It does not exclude any $x_8\ge126$.

## Replay

    sha256sum -c SHA256SUMS
    python3 cap_rank_bins.py
