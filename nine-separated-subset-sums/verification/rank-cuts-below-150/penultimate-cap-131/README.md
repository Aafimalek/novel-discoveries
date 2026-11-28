# Below 150, the penultimate weight is at least 132

For nine sorted positive real weights with pairwise unit-separated subset
sums, **$149\le x_9<150$ implies $x_8\ge132$**. This directly excludes
the cap $t=131$ on $\lfloor x_8\rfloor$ without numerical dependence on
any lower cap. It uses the previously established geometric rank runs,
moment bound and three-deficit interval method; see the
[cap-127](../penultimate-cap-127/README.md) and [cap-130](../penultimate-cap-130/README.md)
proofs.

[Paper (PDF)](paper/orbit-packing-cap131.pdf) · [TeX](paper/orbit-packing-cap131.tex)

The forced rank starts are 142 through 172, with slots $q=34,\dots,64$.
The common counts are $64\le a\le74$ and $b=148-a$. Each
$\alpha_q=u_{a-q+1}$ lies in $[149-2q,151-2q)$. The resulting
bins for the 128 complementary signs are:

| Half-open range | Capacity |
|---|---:|
| [1,21) | $a-64$ |
| each [149−2q,151−2q), q from 64 down to 34 | 1 |
| [83,217) | 33 |
| [278,321) | $148-2a$ |
| [381,10000) | $a-20$ |

The two wide gaps have width at least
$\alpha_{34}-\alpha_{64}+4\ge64$. The total deficit relative to
$y=(125,\ldots,132)$ is $R=\sum_i(y_i-x_i)$. If a prescribed form
is unbalanced, its cap magnitude is at least 242 rather than
below 83, so $R>159$. Otherwise $\alpha_{34}\ge81$ is balanced,
and its cap magnitude is at most 16, so $R\ge65$.
Thus $R\ge65$ in either case.

## Sign orbit packing in deficit cells

Write $W=32$, half the certified wide-gap width. For a base coordinate
strictly smaller than $W$, flipping its sign changes absolute magnitude
by less than $2W$; the same holds for swapping signs at adjacent weights
whose difference is strictly smaller than $W$. Either operation therefore
preserves each set of signs below either wide gap. There is a nonsmall
coordinate since otherwise all eight-coordinate magnitudes would be below
$8W$, contrary to the last bin's lower bound and positive capacity.
Representing complementary pairs by fixing that coordinate's sign
shows that if $s$ coordinates are smaller than $W$, then $2^s$ divides
$a,b$ and hence 148. Therefore $s\le2$, $x_3\ge32$, and the ordered
deficits cap the third deficit at $127-32=95$. On cells which certify
one or two small coordinates, use the implied divisibility too.

The exact checker bounds each fixed deficit by its interval endpoints
and bounds each remaining ordered deficit separately. If the remaining
tail has $N$ entries capped at $c$ and total in $[L,U]$, its $j$-th
entry is at least $(L-(j-1)c)/(N-j+1)$ and at most $U/j$.
Safe outward rounding gives estimates sufficient to certify some flips
and adjacent swaps throughout the whole cell. An adjacent gap is
$1+r_i-r_{i+1}$, so its upper endpoint must be **strictly** below $W$
before adding the generator. The generator action on complementary
sign pairs is computed by restoring the first sign to plus when necessary.

The orbits of the certified generators must each belong entirely to
one of three broad regions: ranks at most $a$, strictly between counts
$a$ and $b$, or above count $b$. Their exact capacities are
$a,b-a,128-b$. A two-dimensional bitset dynamic program asks whether
unrestricted orbit sizes can fill these capacities. If so, construct
the usual outward absolute magnitude interval for each sign (fixed
deficit boxes and prefix-sign averages on the ordered tail). Each
orbit may take only broad region labels that are possible for
**every** sign in that orbit according to these intervals.
The same exact bitset recurrence with the allowed labels checks this
necessary condition. Ordinary full-bin interval matching is checked
independently. This deliberately uses relaxations; rejecting any one
is sufficient, and passing one is not deemed feasible.

## Exact replay

    sha256sum -c SHA256SUMS
    python3 caps_orbit.py 131

The two-deficit stages leave 7,328 profiles. In the third refinement,
299 are rejected by divisibility without splitting. The 279,322 third
cells are all excluded: 624 by tail/moment, 139,190 by unrestricted
orbit sizes, 40,707 by exact interval requirements, and 98,801 by
the interval-conditioned orbit assignments. No profiles remain.
Standard Python only; run succeeded under a 35-second time guard
and a 143,000 KiB virtual-memory guard. No Lean or remote solver
was used for this packet.
