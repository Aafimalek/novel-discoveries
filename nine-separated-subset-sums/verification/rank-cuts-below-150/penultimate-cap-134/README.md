# Below 150, the penultimate weight is at least 135

For nine sorted positive real weights with pairwise unit-separated subset
sums, **$149\le x_9<150$ implies $x_8\ge135$**. This excludes the
branch $134\le x_8<135$ given the independently replayed
[cap-133 theorem](../penultimate-cap-133/README.md), which supplies $x_8\ge134$.
The largest-weight interval itself remains unresolved.

[Paper (PDF)](paper/anchored-tail-cap134.pdf) · [TeX](paper/anchored-tail-cap134.tex) · [Complete replay archive](anchored-tail-replay.tar.gz)

The root replay recomputed the exact phase-two payload and all 140 shards, matching each of the 178 stored intermediate and final records byte for byte. Extract the replay archive before running the full checks.

## Cap-specific implications

The cap $t=134$ forces coordinate-9 starts 145 through 172, so the
unsigned full-sign slots are $q=37,\dots,64$. The magnitudes
$\alpha_q=u_{a-q+1}\in[149-2q,151-2q)$ are consecutive, with common
$64\le a\le74$ and $b=148-a$. The established plus-two endpoints
then give the capacity ranges:

| Half-open magnitude range | Capacity |
|---|---:|
| [1,21) | $a-64$ |
| each [149−2q,151−2q), q from 64 down to 37 | 1 |
| [77,223) | 36 |
| [278,321) | $148-2a$ |
| [375,10000) | $a-20$ |

The two wide gaps have width at least
$\alpha_{37}-\alpha_{64}+4\ge58$. Flipping a sign at a weight
strictly below 29, or swapping signs at adjacent weights with a
gap strictly below 29, preserves membership at both cuts.
The small-flip orbits on complementary sign pairs give
$2^s\mid a,b$ for the number s of such small weights, hence
$2^s\mid148$ and $s\le2$. A nonsmall coordinate exists because
otherwise every absolute signed magnitude is below $8\cdot29<375$.
Thus $x_3\ge29$. Expanded zero-based positions [0,a), [a,b),
and [b,128) retain their exact capacities; an empty middle group
for a=b permits no middle label.

Let $y=(128,\dots,135)$, $r_i=y_i-x_i$, and $R=\sum r_i$.
Balanced magnitudes at y are at most 16 and unbalanced magnitudes
at least 248. If some required form is unbalanced, then $R>171$
because all required magnitudes are below 77. Otherwise
$\alpha_{37}\ge75$ is balanced, so $R\ge59$. Therefore $R\ge59$
in either case, and $r_3\le130-29=101$.
The prior theorem supplies $x_8\ge134$, hence **$r_8\le1$**.
For an ordered deficit tail of length N with sum T, subtract
$r_8$ from each entry and use the extremal prefix-sign averages
of the first N−1 entries. The signed tail is enclosed by the
corresponding endpoint expressions
$\mu T+(\sum\sigma-N\mu)r_8$ over the tail interval and
$0\le r_8\le\min(1,T_{\rm upper}/N)$, with outward rounding.

## Deterministic coverage and exact results

The 8,128 initial unit cells leave 7,223 before splitting by a.
Of 79,453 two-deficit count profiles, 36,615 fail pure orbit
size, 4,644 fail interval tests, and 21,070 fail the
interval-conditioned orbit assignment, leaving **17,124**.
The exact canonical payload is split into **140 disjoint shards**
of at most 128 profiles; it includes exactly every case that the
first two stages did not reject.

All **140** clear with exact refinement: 102 at depth 3 and 38 at
depth 4. Summing the guarded worker logs gives:

| Depth | Refined cells | Orbit-size rejects | Ordinary interval rejects | Interval-conditioned orbit rejects | Residual |
|---|---:|---:|---:|---:|---:|
| 3 | 825,854 | 199,181 | 110,392 | 510,489 | 5,792 |
| 4 | 191,000 | 131,157 | 24,219 | 35,624 | 0 |

A lightweight independent audit checks the exact disjoint
partition, source pins, and the upstream and downstream digest of
each completed depth. The separate arithmetic audit reconciles all
178 recorded depth logs against the exact progress counts. An
independent fresh run can recompute the actual proof arithmetic.

## Replay

    sha256sum -c SHA256SUMS
    python3 parameters134.py
    python3 coverage_audit.py
    python3 arithmetic_totals.py
    ./replay-all.sh

The final script copies pinned source and checkpoint to a fresh
temporary directory, reruns phase 2 and checks canonical byte equality,
and recomputes all 140 shards serially with no reuse of old progress.
Each proof invocation is bounded by 35 seconds and 143,000 KiB of
virtual memory; memory and disk reserves are checked between shards.
All the computations are standard Python integer or fraction
arithmetic. The geometric implications are handwritten; this is not
a Lean theorem or an exclusion of any candidate with $x_8\ge135$.
