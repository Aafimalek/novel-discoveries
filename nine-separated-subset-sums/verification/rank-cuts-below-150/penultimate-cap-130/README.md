# Below 150, the penultimate weight is at least 131

For nine sorted positive real weights with pairwise unit-separated subset
sums, **$149\le x_9<150$ implies $x_8\ge131$**. This is a direct
exclusion of the cap $t=130$ on $\lfloor x_8\rfloor$, so no prior
cap's numerical replay is needed. The dependencies are the established
geometric rank runs, sign moments, and exact three-deficit interval
matching proofs in the [cap-127](../penultimate-cap-127/README.md) and
[general rank-hole proof](../wide-hole-orbits/README.md).

[Paper (PDF)](paper/permutation-orbit-cap130.pdf) · [TeX](paper/permutation-orbit-cap130.tex)

The forced rank edges run from 141 through 172, giving slots
$q=33,\dots,64$. The base unsigned magnitudes at these slots obey
$\alpha_q=u_{a-q+1}\in[149-2q,151-2q)$, for common
$64\le a\le74$ and $b=148-a$. The bins are:

| Half-open range | Capacity |
|---|---:|
| [1,21) | $a-64$ |
| each [149−2q,151−2q), q=64 down to 33 | 1 |
| [85,215) | 32 |
| [278,321) | $148-2a$ |
| [383,10000) | $a-20$ |

The two wide gaps at ranks $a,b$ have width at least
$\alpha_{33}-\alpha_{64}+4\ge66$, by the plus-two endpoints.
As before, flips at any weight below 33 preserve membership at both
cuts. Their orbit sizes divide both $a$ and $b$, giving $x_3\ge33$.
At the cap vector $y=(124,\dots,131)$, balanced forms have magnitude
at most 16 and unbalanced forms at least 240. If any prescribed form
is unbalanced then the total deficit $R=\sum_{i\le8}(y_i-x_i)>155$
because every prescribed form is below 85. Otherwise
$\alpha_{33}\ge83$ is balanced and $R\ge67$. Thus $R\ge67$
and the third deficit bound $r_3\le126-33=93$ are used.

## Exact matching and one final permutation cut

* The initial 7,626 unit cells leave 6,718 after tail/slot matching.
* Splitting by the eleven counts $a$ gives 73,898 profiles;
  all-sign interval matching leaves 3,239.
* Divisibility removes 36 of those profiles without refinement.
  The rest give 115,315 third-deficit unit cells. The moment/tail
  bounds remove 670 and all-sign capacity matching removes 114,644.
  The unique remaining cell has $a=64$, $r_1\in[49,50]$,
  $r_2,r_3\in[24,25]$.

For this cell, the first two adjacent gaps between weights are at
most 27 and 2 respectively. The others are at most 26 since the
deficits are nonnegative nonincreasing and $r_3\le25$.
All seven adjacent gaps are therefore strictly below 33.
Swapping signs of adjacent weights changes the absolute magnitude
by at most twice their weight gap, which is strictly below 66.
It therefore cannot change membership at either wide magnitude
gap. Since adjacent swaps generate all coordinate permutations,
both subsets of signed forms counted by $a$ and $b$ are unions of
the permutation orbits on the 128 complementary sign pairs.

These five orbits are indexed by the smaller of the number of
plus and minus signs: their sizes are $1,8,28,56,35$ from the binomial
coefficients, halving the four-plus orbit at complementation.
The union for $a$ must be included in the union for $b$.
Assigning each orbit to the first union, the second union only, or
neither gives $3^5$ finite choices. None gives $(a,b)=(64,84)$.
This excludes the last residual cell and completes the cap.

## Exact replay

    sha256sum -c SHA256SUMS
    python3 finish130.py

This is standard-Python integer and fraction arithmetic with
handwritten geometric implications. It is not a Lean proof, an
exclusion of candidates with $x_8\ge131$, or an improvement on
the known full range for the largest weight.
