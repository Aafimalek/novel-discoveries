# Below 150, the penultimate weight is at least 133

For nine sorted positive weights with pairwise unit-separated subset sums,
**$149\le x_9<150$ implies $x_8\ge133$**. This excludes the branch
$132\le x_8<133$ after the independently replayed
[cap-131 theorem](../penultimate-cap-131/README.md) already gives $x_8\ge132$.
In contrast to earlier cap packets, that lower bound is used here
to sharpen the tail intervals. The largest-weight interval itself
is not excluded.

[Paper (PDF)](paper/anchored-tail-cap132.pdf) · [TeX](paper/anchored-tail-cap132.tex) · [Complete replay archive](anchored-tail-replay.tar.gz)

Extract the archive for the full frozen inputs and per-shard logs. An independent fresh run reproduced the exact phase-two data and cleared all 70 shards.

## Cap-specific inequalities

For cap $t=132$ the forced coordinate-9 starts are 143 through 172,
so $q=35,\dots,64$. The common counts are $64\le a\le74$ and $b=148-a$,
and $\alpha_q=u_{a-q+1}\in[149-2q,151-2q)$ are consecutive base unsigned
full sign magnitudes. With the earlier plus-two endpoints, the
capacity ranges for all 128 complementary signs are:

| Half-open magnitude range | Capacity |
|---|---:|
| [1,21) | $a-64$ |
| each [149−2q,151−2q), q from 64 down to 35 | 1 |
| [81,219) | 34 |
| [278,321) | $148-2a$ |
| [379,10000) | $a-20$ |

The two holes have width at least $2(64-35)+4=62$. A flip at weight
strictly below 31 or a swap at adjacent weight gap strictly below 31
preserves each broad group with rank indices in [0,a), [a,b), or
[b,128); these are zero-based position sets after expanding each bin
by its capacity. Empty bins, including the middle broad group if
a=b, add no positions. Small flip orbits give $x_3\ge31$ since
$2^s\mid a,b$ would imply $2^s\mid148$ and $s\le2$.

For $y=(126,\dots,133)$ write $r_i=y_i-x_i$ and $R=\sum r_i$.
Unbalanced signed magnitudes at y are at least 244 and balanced
ones at most 16. If any prescribed sign is unbalanced, then
$R>244-81=163$. Otherwise the balanced $\alpha_{35}\ge79$
gives $R\ge63$. Hence in all cases $R\ge63$.

## The anchored tail and finite worker proof

The previous cap proof gives $x_8\ge132$, so the last deficit is
$z=r_8\le1$. For any ordered tail of N deficits with total T,
subtract z from all entries, making the last entry zero. By
prefix differences, the signed contribution of the first N−1
residual entries lies between their extreme prefix-sign averages
$\mu$ times $T-Nz$. After adding back the common contribution,
the bounding expression is
$\mu T+(\sum\sigma-N\mu)z$.
Use the tail interval for T and $0\le z\le\min(1,T_{\rm upper}/N)$
to bound the terms independently, rounding outward. This is a
safe relaxation even if the two extrema cannot occur together.

The two-deficit stage starts with 7,875 unit cells; 6,966 reach
the count splits. Across 76,626 count profiles, there are 38,640
pure orbit-size rejections, 2,610 individual interval rejections,
and 26,950 interval-conditioned orbit rejections, leaving **8,426**.
The ordinary interval and sign-orbit packing arguments are the
same as in cap 131. Refine each of the 8,426 cases by the third
deficit (and, only when needed, the fourth), retaining the
anchored signed bounds.

A deterministic phase-2 replay generated the exact residual
profile payload, which is split into **70 disjoint exhaustive shards**
of at most 128 inputs each. All 70 complete with zero residual:
67 at depth 3 and three at depth 4. In aggregate:
* Depth 3 covers 387,410 cells: 123,021 orbit-size rejections,
  62,657 ordinary interval rejections, 201,702 interval-conditioned
  orbit rejections, and 30 residual cells.
* Depth 4 covers 952 refinements of those 30 cells: 818, 52, and
  82 by the respective three tests, with none remaining.

The earlier monolithic run timed out and is not used for third-stage
coverage. Each accepted shard has a separately retained log and an
input/output SHA chain from the exact phase-2 payload. One worker
ran at a time, with 35-second and 143,000-KiB virtual-memory guards
per invocation.

## Independent audit and replay

    sha256sum -c SHA256SUMS
    python3 coverage_audit.py
    ./replay-all.sh

The first two commands independently check source/payload/manifest
integrity, disjoint full shard coverage, and that all stored chains
end empty. For a fresh exact computation, the last command first
reruns phase 2 and compares its canonical byte payload; then it
serially recomputes all 70 shards to a fresh results directory.
An individual shard can instead be run with a separate results
directory using the in-packet run-shard.sh wrapper. Nothing in
the verifier depends on third-party solver output or floating
arithmetic. The mathematical rank and endpoint implications are
handwritten, not a Lean theorem.
