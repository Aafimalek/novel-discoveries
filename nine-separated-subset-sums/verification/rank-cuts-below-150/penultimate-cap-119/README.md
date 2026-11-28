# Below 150, the penultimate weight is at least 120

If nine sorted positive real weights have 1-separated subset sums and
$149\le M=x_9<150$, then **$x_8\ge120$**. This is an exclusion of the
penultimate-weight shard $x_8<120$, not of the whole interval for $x_9$.
The prior forbidden rank-149 edges and certified eight Harper cut sizes
are mathematical premises, as in the [preceding rank-slot proofs](../rank-slot-moment/) and [rank-run derivation](../hall-rank-runs/).
The new arithmetic and matching are exact Python.

## A cap forces an entire rank-edge run

Let $t$ be any integer bound for $\lfloor x_8\rfloor$. At each Harper cut
$k$ in 158,159,161,162,168,169,171,172, every rank $k+1,\dots,k+148$
is an external neighbor, by the established forbidden-band saturation.
For $j$ with $\max(k+t+1,257)\le j\le k+148$, the edge from before the
cut to $j$ must change coordinate 9: its rank length exceeds $t$.
Its length is at most 148, because a length-149 edge would begin at
$j-149$ in the forbidden rank band. The lower ranks obtained by
subtracting $M$ strictly increase with $j$, are at least $j-148$, and
end at $k$. Consequently each lower rank is exactly $j-148$. This
forces every start from $\max(109,k+t-147)$ through $k$.
The unions for $t\le119$ considered here are single runs, as the
replay checks. Their associated full-sign slots $q=k-108$ run from
$\max(109,158+t-147)-108$ to 64.

## Strengthened rank-slot moment

Write $u_1<\cdots<u_{128}$ for the absolute eight-weight full-sign
values (complementary signs counted once), and $N(v)=\#\{i:u_i<v\}$.
The $u_i$ and the corresponding nine-weight magnitudes $d_i$ each
have consecutive spacing at least 2. A forced start with slot $q$
gives $\alpha_q=u_{j_q}$ with
$149-2q\le\alpha_q<151-2q$ and full-sign positions $q$ and $149-q$
at $M-\alpha_q$ and $M+\alpha_q$. Set
$a_q=N(2M-\alpha_q)$ and $b_q=N(2M+\alpha_q)$.
Ranking the two full forms gives
$a_q+b_q=148$ and $j_q=a_q-q+1$.
Since the $\alpha_q$ strictly decrease, the $a_q$ are nondecreasing
but $a_{q+1}-a_q\le0$ for consecutive slots. Thus all $a_q=a$
along the run, with $64\le a\le74$.

The next $u_{a+1}$ is strictly above $2M-\alpha_q$, and the
full form $u_{a+1}-M$ must lie at least 2 above $M-\alpha_q$.
The same reasoning at $2M+\alpha_q$ compares to
$M+\alpha_q$. Therefore the following are valid point bounds:

    u[a-q+1] ≥ 149−2q
    u[a+1]   ≥ 150+2q
    u[149-a] ≥ 449−2q.

Each bound advances by at least 2 per rank; also $u_j\ge2j-1$.
The exact profiles for all $64\le a\le74$ give the moment
$\sum_{i=1}^8 x_i^2=\sum_j u_j^2/128$ by sign averaging. Only lower
envelopes are used; no assumption that such a profile is attainable.

## Excluding caps through 118

Write $y=(t-6,\ldots,t+1)$, so $x_i\le y_i$ for $i\le8$.
Put $r_i=y_i-x_i$ and $R=\sum r_i$. The deficits are nonincreasing
and nonnegative by singleton spacing. If $B$ is the moment lower
bound, the squared loss $D=\sum y_i^2-B$ is an upper bound for
$\sum_i (2y_i r_i-r_i^2)$. Negative $D$ immediately excludes the
cap; this works for the full $x_8<110$ shard at $t=109$, and for
$t=110$. For the later caps $R\le D/y_1$ because $r_i\le y_i$.

At $y$ the balanced signs (four plus, four minus) have magnitudes
at most 16. All other signs have magnitude at least $2t-20$,
achieved by taking the smallest five positive. Replacing $y$ by
$x$ moves every magnitude by at most $R$. For caps 111–119 the
forced $\alpha_{64}<23$ cannot come from an unbalanced sign, by
the coarse $R$ bound. Hence for some balanced sign
$|\sum_i \sigma_i r_i|\le39$. As each $r_i$ lies on one of the two
sides, $r_i\le (R+39)/2$. For $R\ge39$ this gives
$\sum_i r_i^2\le (R^2+39^2)/2$: if the largest entry is at most
$R/2$, use $\sum r_i^2\le R^2/2$; otherwise concentrate the
remaining mass into one entry and increase the largest to its
upper bound. For $R\le39$ simply use $\sum r_i^2\le R^2$.
Consequently $D\ge 2y_1R-\sum r_i^2$ gives the exact integer
cutoffs used by the replay. Both pieces are increasing on the
relevant intervals (the low piece starts with $y_1>39$ and the
high piece ends below $2y_1$).

There are 35 balanced complementary sign pairs. At slot $q$, at
least $a-q+1\ge65-q$ base magnitudes are below $151-2q$.
A cap admits at most 35 plus the number of unbalanced $y$
magnitudes below $151-2q+R$ in that region. This exact count
excludes every cap from 111 through 118. For cap 119 it gives
$R<144$ but not a contradiction.

## Exact two-deficit boxes for cap 119

In this cap there are 43 distinct required $\alpha$ slots. At
least 8 have unbalanced sign. If $R\le125$, an unbalanced form
has magnitude at least $218-125=93$. Only the seven slots
$q=22,\ldots,28$ can reach 93 (slot 29 has strict upper 93).
Thus $R>125$; the box replay relaxes to $R\ge125$.

The deficits $r_1,r_2$ lie in $[0,112]$. Cover them by unit cells
$[A,A+1]\times[B,B+1]$ with integer $B\le A$. This covers all
ordered pairs, including integral boundaries. Let $T=r_3+\cdots+r_8$.
Taking the lower endpoints $r_1=A$ and $r_2=B$, the first two
minimum squared losses are $2y_1A-A^2$ and $2y_2B-B^2$,
since squared loss is increasing for $r_i\le y_i$.
Each tail entry is at most $B+1$, so its loss is at least
$(2y_3-B-1)r_i$. This gives the rational upper bound for $T$.
The constraints $125\le R\le144$ and $0\le T\le6(B+1)$ give
the other simple bounds. All upper interval rounding is outward.

For a fixed sign pattern, inverse-prefix differences express
the sorted tail deficits as a nonnegative linear combination
of initial-segment indicators. For each indicator take the
average of its signs. Consequently the signed contribution
of the tail lies between $T$ times the least and greatest
of its six prefix-sign averages. All these averages have
denominator dividing 60. Combining with the first two deficit
intervals and $y$ bounds each full-sign magnitude by an interval.
Its eligible $q$ slots form an integer interval, since
$\alpha_q\in[149-2q,151-2q)$.
Every required slot must be matched to a different one of the
128 complementary full sign pairs; there is no reliance on
simultaneous realizability of this outer approximation.

The replay attempts exact interval matching, in ascending $q$,
choosing an eligible interval with smallest right endpoint.
The greedy rule is complete by exchange: if an assignment uses
a different interval at the current $q$, move the earliest-deadline
interval to $q$ and put the displaced one at its previous later
slot, if any. This is valid because the displaced interval
contains the current $q$ and ends no earlier than the chosen one.
All 6,328 cells are excluded: 1,597 by moment loss, 2,631 by
tail bounds, and 2,100 by interval matching. No heavy solver,
floating comparison, or proof kernel is used for this replay.

## Reproduce

    sha256sum -c SHA256SUMS
    python3 cap_moment.py
    python3 cap119_box.py

This packet does not assert an exclusion for $x_8\ge120$, nor an
improvement of the global nine-weight optimum interval.
