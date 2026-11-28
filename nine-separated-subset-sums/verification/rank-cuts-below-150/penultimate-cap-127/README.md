# Below 150, the penultimate weight is at least 128

For nine sorted positive real weights with 1-separated subset sums,
**$149\le x_9<150$ implies $x_8\ge128$**. This is the direct cap
$t=127$ on $\lfloor x_8\rfloor$, and includes all smaller caps.
It relies on the prior forbidden length-149 band, eight exact Harper cuts,
and the general moment, deficit and interval matching proofs in the
[cap-119](../penultimate-cap-119/README.md), [cap-120](../penultimate-cap-120/README.md)
and [cap-124](../penultimate-cap-124/README.md) packets. It does not rely on
their numerical cap replays or imply an increase in the lower bound
on the largest weight.

## Rank slots and capacity bins at cap 127

The eight Harper cuts force coordinate-9 rank edges of length 148
at every start from 138 to 172. Thus the consecutive full-sign slots
are $q=30,\ldots,64$, with common counts $64\le a\le74$,
$b=148-a$. The $\alpha_q$ are at exact positions $a-q+1$
among the 128 absolute eight-coordinate sign values $u_j$. Each
lies in $[149-2q,151-2q)$, and consecutive $u$ spacing is at least 2.
The established plus-two bounds around $2M\pm\alpha_q$ give
$u_a<209$, $u_{a+1}\ge278$, $u_b<321$, $u_{b+1}\ge389$.
The resulting bins and capacities are:

| Half-open range | Capacity |
|---|---:|
| [1,21) | $a-64$ |
| each [149−2q,151−2q), q=64 down to 30 | 1 |
| [91,209) | 29 |
| [278,321) | $148-2a$ |
| [389,10000) | $a-20$ |

The endpoints 21 and 91 come from the first and last indexed
$\alpha$ via the minimum spacing to the preceding or following
unprescribed magnitude. The final endpoint is loose since the
sum of the eight coordinate caps is 996.

Put $y=(121,\ldots,128)$, $r_i=y_i-x_i$, $R=\sum r_i$.
Since only 35 slots are now required, the earlier unbalanced-sign
count does not prove positive $R$ by itself. The first two replay
stages use **no extra lower bound on $R$**. For the last stage,
either some required slot uses an unbalanced form, whose cap
magnitude is at least 234, whereas all slots lie strictly below 91
(giving $R>143$); or every required slot is balanced, whose cap
magnitudes are at most 16. In the latter case $\alpha_{30}\ge89$
requires $R\ge73$. In either case $R\ge73$ is safe.

## Divisibility at both wide magnitude gaps

The two successive gaps at indices $a$ and $b$ have width at least
$\alpha_{30}-\alpha_{64}+4\ge72$. This follows by applying the
upper and lower plus-two bounds with the opposite extreme
$\alpha$ endpoints. If a base weight is smaller than 36, flipping
its sign changes an absolute full-sign magnitude by less than
72, so preserves each of the two sets below the wide gaps.

At least one base weight is at least 36: otherwise every magnitude
is less than 288, contrary to $u_{b+1}\ge389$. Fix the sign of one
such coordinate to represent all complementary pairs once. If
there are $s$ smaller coordinates, the sign-flip orbits are of
size $2^s$, and the memberships just considered are constant on
each orbit. Therefore $2^s$ divides both $a$ and $b$, hence divides
148; thus $s\le2$ and **$x_3\ge36$**. If a deficit box certifies
that either of the first two weights is below 36, the corresponding
divisibility also applies to the profile's count $a$.

## Three-stage exact replay

1. The ordinary two-deficit cover uses all 7,260 integer unit cells
   for $(r_1,r_2)$, with no extra lower bound on $R$. Slot-only
   matching rejects 931 cells, leaving 6,329.
2. Expand each to all 11 candidate counts $64\le a\le74$ and
   apply the profile-specific moment loss, tail bounds, and
   full capacity matching. Of the 69,619 profiles, just
   94 remain: 45 for $a=64$, 29 for $a=65$, 15 for $a=66$,
   5 for $a=67$.
3. Only on these 94 profiles, cover the third deficit by a unit
   interval $[C,C']$ with integer $C$, $C'=\min(C+1,87)$.
   This covers every possibility because $r_3\le r_2$ and
   $r_3\le123-36=87$. Use the new lower bound $R\ge73$,
   and subtract the third deficit interval from the previous
   tail interval to enclose the new five-coordinate tail.
   The new moment loss subtracts at least $2y_3 C-C^2$ for
   the third deficit, and each remaining deficit at most $C'$
   contributes loss at least $(2y_4-C')r_i$.
   Apply the same outward-rounding, prefix averaging and
   interval capacity matching to the five remaining deficits.
   No profiles are pruned by divisibility alone; the added
   $r_3$ cap and deficit cover give 2,397 cases. Loss/tail
   bounds reject 262, and all other 2,135 fail full capacity
   matching. No cases remain.

All three stages use standard Python, exact integer or rational
bounds, and complete interval matching within the declared
relaxations. The proofs of the geometric implications are
handwritten. No finite case beyond $x_8<128$ is excluded here.

## Reproduce

    sha256sum -c SHA256SUMS
    python3 cap127_third.py
