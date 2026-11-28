# Below 150, the penultimate weight is at least 136

For nine sorted positive real weights with pairwise unit-separated subset
sums, **$149\le x_9<150$ implies $x_8\ge136$**. This excludes the
branch $135\le x_8<136$ given the independently replayed
[cap-134 theorem](../penultimate-cap-134/README.md), which supplied $x_8\ge135$.
The full largest-weight interval remains unresolved.

[Paper (PDF)](paper/anchored-tail-cap135.pdf) · [TeX](paper/anchored-tail-cap135.tex) · [Complete replay archive](anchored-tail-replay.tar.gz)

A fresh independent run reproduced exact phase two and all 181 shards, matching all 253 stored progress records byte for byte. Extract the archive for the full checks.

## Cap-specific implications

The cap $t=135$ forces coordinate-9 starts 146 through 172, so the
unsigned full-sign slots are $q=38,\dots,64$. The magnitudes
$\alpha_q=u_{a-q+1}\in[149-2q,151-2q)$ are consecutive, with common
$64\le a\le74$ and $b=148-a$. The established plus-two endpoints
then give the capacity ranges:

| Half-open magnitude range | Capacity |
|---|---:|
| [1,21) | $a-64$ |
| each [149−2q,151−2q), q from 64 down to 38 | 1 |
| [75,225) | 37 |
| [278,321) | $148-2a$ |
| [373,10000) | $a-20$ |

The two wide gaps have width at least
$\alpha_{38}-\alpha_{64}+4\ge56$. Flipping a sign at a weight
strictly below 28, or swapping signs at adjacent weights with a
gap strictly below 28, preserves membership at both cuts.
The small-flip orbits on complementary sign pairs give
$2^s\mid a,b$ for the number s of small weights, hence
$2^s\mid148$ and $s\le2$. A nonsmall coordinate exists because
otherwise every absolute signed magnitude is below $8\cdot28<373$.
Thus $x_3\ge28$. Expanded zero-based positions [0,a), [a,b),
and [b,128) retain their exact capacities; an empty middle group
for a=b permits no middle label.

For $y=(129,\dots,136)$ write $r_i=y_i-x_i$, $R=\sum r_i$.
Balanced magnitudes at y are at most 16 and unbalanced ones at
least 250. If any required form is unbalanced, $R>175$ because
its magnitude is below 75. Otherwise $\alpha_{38}\ge73$ is
balanced and $R\ge57$. Thus $R\ge57$ in either case, and
$r_3\le131-28=103$. The prior theorem supplies $x_8\ge135$, hence
**$r_8\le1$**. For an ordered deficit tail of length N with sum T,
subtract $r_8$ from each entry and use the extreme prefix-sign
averages of the first N−1 entries. The signed tail is bounded by
the corresponding endpoint expressions
$\mu T+(\sum\sigma-N\mu)r_8$ over the T interval and
$0\le r_8\le\min(1,T_{\rm upper}/N)$, rounding outward.
No optional additional tail cuts are used in the actual baseline.

## Deterministic coverage and exact results

The 8,256 initial unit cells leave 7,360 before splitting by a.
Of 80,960 two-deficit count profiles, 35,600 fail pure orbit size,
3,547 fail ordinary interval tests, and 19,181 fail the
interval-conditioned orbit assignment. The canonical residual is
**22,632** profiles, which the manifest partitions into **181**
disjoint exhaustive shards of at most 128 profiles.

All **181** clear with exact refinement: 109 at depth 3 and 72
at depth 4. Summing the guarded worker logs gives:

| Depth | Refined cells | Orbit-size rejects | Ordinary interval rejects | Interval-conditioned orbit rejects | Residual |
|---|---:|---:|---:|---:|---:|
| 3 | 1,119,917 | 249,659 | 142,052 | 711,965 | 16,241 |
| 4 | 549,098 | 306,509 | 89,564 | 153,025 | 0 |

A lightweight independent audit checks the complete disjoint partition,
each source pin, and the upstream and downstream digests of each
completed depth. A separate arithmetic audit reconciles all 253
recorded depths with their exact rejection logs and residual counts.
The hashes preserve the proof artifacts; they do not replace
replaying the arithmetic.

## Replay

    sha256sum -c SHA256SUMS
    python3 parameters135.py
    python3 coverage_audit.py
    python3 arithmetic_totals.py
    ./replay-all.sh

The last script copies the pinned source and checkpoint to a fresh
temporary directory, reruns phase 2 to demand canonical byte equality,
and recomputes all 181 shards serially with no reuse of old progress.
Each proof invocation is bounded by 35 seconds and 143,000 KiB
virtual memory, and memory and disk reserves are checked between
shards. It uses only the Python standard library and exact integer
or fraction arithmetic. The geometric implications are handwritten;
this is not a Lean theorem, a new upper witness, or an exclusion of
any candidate with $x_8\ge136$.
