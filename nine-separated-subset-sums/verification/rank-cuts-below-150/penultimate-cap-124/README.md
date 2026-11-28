# Below 150, the penultimate weight is at least 125

For nine sorted positive real weights with 1-separated subset sums,
**$149\le x_9<150$ implies $x_8\ge125$**. This strengthens the
earlier cap-119 and cap-120 replays. It is a direct exclusion for
$t=124$ as an upper bound on $\lfloor x_8\rfloor$, so it excludes
all smaller caps without using those earlier replay results.

The proof uses the prior forbidden length-149 edges and Harper-cut
sizes, as well as the [cap-119 proof](../penultimate-cap-119/README.md)'s general
rank-run, plus-two bound, deficit intervals, and interval-matching
argument. The narrower [cap-120 proof](../penultimate-cap-120/README.md)
has the corresponding derivation of the full capacity bins. These
inputs are handwritten geometry with exact finite replays, not a
complete Lean proof of the cap theorem.

## The cap 124 data

The runs for the eight Harper cuts merge into the contiguous
rank-148 starts from 135 through 172. Thus the forced absolute
base signed-sum slots are $q=27,\ldots,64$. The common threshold
counts are $64\le a\le74$ and $b=148-a$.

For each q, one magnitude $\alpha_q=u_{a-q+1}$ lies in
$[149-2q,151-2q)$. Consecutive base magnitudes have spacing at
least 2. Therefore entries before the run are all strictly below
21 (since $\alpha_{64}<23$), and those after the run are at least
97 (since $\alpha_{27}\ge95$). Using the +2 signed threshold
bounds around $2M-\alpha$ and $2M+\alpha$ at the extreme q gives

    u_a < 203,    u_{a+1} >= 278,
    u_b < 321,    u_{b+1} >= 395.

For example $u_a\le2M-\alpha_{27}-2 <300-95-2=203$; the other three
follow from $\alpha_{64}<23$, $\alpha_{27}\ge95$, and the same
plus-two bounds. Thus all 128 absolute complementary base forms
must be assigned to the following bins, in order:

| Half-open range | Capacity |
|---|---:|
| [1,21) | $a-64$ |
| each [149−2q,151−2q), q=64 down to 27 | 1 |
| [97,203) | 26 |
| [278,321) | $148-2a$ |
| [395,10000) | $a-20$ |

The loose final endpoint is valid because even the total of
the eight coordinate caps is only 972. Omitted ranges are forbidden.

## Exact coverage of the deficit boxes

Let $y=(118,\ldots,125)$ and $r_i=y_i-x_i$. The deficits are
nonnegative, nonincreasing, and each at most 117. Among the 38
required slot magnitudes at least three are unbalanced (there are
only 35 balanced complementary signs). At y the smallest unbalanced
magnitude is 228. If $R=\sum r_i\le135$, all unbalanced magnitudes remain
at least 93, but only slots q=27,28 can reach 93. Consequently
$R>135$; replay safely uses $R\ge135$.

The two-deficit interval cover and conservative outward rounding
are exactly as in the cap-119 packet. For each count $a$ the new
envelope bounds the moment, and hence gives a permitted loss budget
$D=\sum y_i^2-\sum u_{\rm lower}^2/128$. With $c=117$ and
$R=kc+s$ ($k$ an integer, $0\le s<c$), the upper bound on
$\sum r_i^2$ is $kc^2+s^2$. This follows by moving mass from any
two nonendpoint coordinates toward the larger one until one is
0 or c, increasing the squared sum at each step. Thus the squared
loss is at least $2y_1R-kc^2-s^2$, a globally increasing piecewise
quadratic because the derivative on each segment is
$2y_1-2s>0$. This gives the exact integer loss cutoffs, followed
by the balanced-sign refinement where its hypothesis holds.
Assignments are interval matching to consecutive unit positions
after expanding each capacity bin; the earlier exchange proof
applies without changes.

The actual results are:

* Stage 1: 6,903 unit cells; tail bounds reject 1,059 and
  slot-only matching rejects 749; 5,095 go to the second stage.
* Stage 2: expand to 56,045 cell/count pairs; 101 fail
  the profile loss/tail check and 55,944 fail full capacity
  matching. None remain.

## Replay

    sha256sum -c SHA256SUMS
    python3 cap_rank_bins.py

The exact replay uses only standard Python, with integer and fraction
arithmetic. It does not prove there is no candidate with $x_8\ge125$.
