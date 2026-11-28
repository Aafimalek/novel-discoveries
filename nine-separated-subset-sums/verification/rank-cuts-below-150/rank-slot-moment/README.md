# Rank-slot moment bounds in the real interval [149,150)

**Scope:** assumes the nine positive, sorted real weights have all
512 subset sums pairwise 1-separated and that $149\le M=x_9<150$.
The [prescribed rank-slot proof](../rank-slot-pilot/README.md) supplies the
eight coordinate-9 edge pairs; these are not available from this
argument for $150\le M<161$. The result is a stronger necessary root
condition, not an exclusion of $[149,150)$ and not an upper witness.

## A moment inequality using all eight prescribed slots

Let $u_1<\cdots<u_{128}$ be the positive absolute full-sign sums
of the first eight weights, one for each pair of complementary
signs. These are positive by unit separation of the first eight
subset sums. They have $u_1\ge 1$ and consecutive spacing at
least 2: orient the two signed vectors to be positive; their
difference is twice a nonzero signed subset-sum difference.
Write $N(t)=\#\{j:u_j<t\}$.

The full nine-weight absolute sign sums, sorted as $d_1,\ldots,d_{256}$,
are the $M+u_i$ and $|M-u_i|$. They are all distinct. For each of the
forced lower rank starts $k=158,159,161,162,168,169,171,172$, the
positions $p=257-k$, $q=k-108$ correspond to $M+\alpha_q$ and
$M-\alpha_q$, where $\alpha_q=u_{j_q}>0$. In particular $p+q=149$.
The relevant forced slots are

    q = 50, 51, 53, 54, 60, 61, 63, 64.

The two ranks defining $d_q$ lie in [172,320]. Its total excess
over unit spacing is $1+\delta$, where $M=149+\delta$, so
$2q-1\le d_q\le 2q+\delta$. Thus
$149-2q\le\alpha_q\le M-2q+1<151-2q$.

Put $a_q=N(2M-\alpha_q)$ and $b_q=N(2M+\alpha_q)$. The rank of
$M-\alpha_q$ is $q=1+a_q-j_q$, since only $|M-u_i|$ can
fall below it, and precisely when $\alpha_q<u_i<2M-\alpha_q$.
The rank of $M+\alpha_q$ is $p=j_q+b_q$: there are $j_q-1$
earlier $M+u_i$ terms and $b_q$ earlier $|M-u_i|$ terms.
No ties at the thresholds occur because the $d_i$ are distinct.
Hence

    a_q + b_q = 148,   j_q = a_q - q + 1,   q ≤ a_q ≤ 74.

For successive prescribed $q<r$, the $\alpha$ values strictly
decrease, so $a_r\ge a_q$ and $j_r\le j_q-1$. Therefore
$0\le a_r-a_q\le r-q-1$. In particular each of the four consecutive
pairs (50,51), (53,54), (60,61), (63,64) shares its $a$-value.

For any allowed tuple, lower bounds on individual positive
magnitudes are

    u[a_q-q+1] ≥ 149-2q
    u[a_q+1]   ≥ 148+2q
    u[149-a_q] ≥ 447-2q.

The last two follow respectively from $2M-\alpha_q\ge M+2q-1$
and $2M+\alpha_q\ge 2M+149-2q$. Every lower bound $u_i\ge z$ gives
$u_j\ge z+2(j-i)$ for $j\ge i$. The exact replay enumerates the
four count choices and takes the maximum lower envelope including
$u_j\ge 2j-1$. It also checks the already-known strict upper slot bounds
against those envelopes (they remove no tuples). Exactly 264 count
tuples pass the arithmetic relaxation; the minimum sum of the 128
squared envelope values is 8,922,135.

For an independent identity, averaging the square of
$\sum_{i=1}^8 \varepsilon_i x_i$ over all full sign choices cancels
every cross term. Grouping complementary signs gives
$\sum_{i=1}^8 x_i^2=128^{-1}\sum_j u_j^2$. Thus
$$
\sum_{i=1}^8 x_i^2\ \ge\ \frac{8922135}{128}
  =69704.1796875,\qquad
\sum_{i=1}^9 x_i^2\ \ge\ \frac{11763863}{128}
  =91905.1796875 .
$$
The enumeration proves a lower bound, not attainability of the
arithmetic relaxation or the original problem.

## Three affine root cuts and a new top-two threshold

1. **Total mass.** If $S_8=\sum_{i=1}^8 x_i\le516.929$, compare
   $x_1,\ldots,x_8$ with
   $y=(1,2,3,4,62.929,147,148,149)$. For each suffix beginning
   at $j\ge6$, $\sum_{i=j}^8 x_i\le\sum_{i=j}^8 y_i$ by the
   upper spacing bounds $x_i\le141+i$. For $j\le5$ it follows
   from the presumed upper total and $x_i\ge i$ for $i<j$.
   Summation by parts with partial tail sums of $y_i-x_i$ and
   nonnegative consecutive increments of $y_i+x_i$ then gives
   $\sum_i x_i^2\le\sum_i y_i^2=69704.059041$, below the moment
   bound. Therefore $S_8>516.929$ and the full total is
   **$S>665.929$**.

2. **Top two among the smaller eight.** Suppose
   $x_7+x_8\le H=192.63$; put $t=x_7\ge84$ by the prior
   independent root cut. Then $t\le(H-1)/2$ by singleton spacing,
   $x_{7-k}\le t-k$ for $k=0,\ldots,6$, and $x_8\le H-t$.
   The square upper bound
   $\sum_{k=0}^6(t-k)^2+(H-t)^2$ is increasing for $t\ge84$
   (its derivative is $16t-42-2H>0$). Evaluating at
   $(H-1)/2$ gives $69703.5138$, below the moment bound.
   Hence **$x_7+x_8>192.63$**, and in particular $x_8>96.815$.

3. **Coordinate secants.** For
   $L=(1,2,3,4,5,44,84,85)$ and $U=(142,143,144,145,146,147,148,149)$,
   the prior root and singleton spacing give $L_i\le x_i\le U_i$.
   Then $x_i^2\le (L_i+U_i)x_i-L_iU_i$ from
   $(x_i-L_i)(U_i-x_i)\ge0$. Summing these upper bounds must
   accommodate the base-eight lower moment.

The LP uses the closed relaxation of the two new strict sum cuts.
On all 218 previously nonexcluded central orientations, this gives
**22 further whole-orientation exclusions**, independently verified
with exact rational Farkas multipliers. Hence 316 of the original
512 orientations have been excluded in this root model, and **196
remain unresolved**. No feasibility assertion is made for those
196. These counts concern whole central orientations, not possible
sign vectors at any individual slot.

## Reproduce

```sh
sha256sum -c SHA256SUMS
python3 rank_moment_arithmetic.py
python3 moment_central_lp.py --verify-only
```

The proofs above are handwritten mathematics. The finite arithmetic
and Farkas checks are executable exact Python with no third-party
dependencies. SciPy is used only in optional certificate generation;
the independent verifier does not use it or trust a floating-point
decision. The code uses the previous standard root and the
opposite-central-sign pairing inequalities as dependencies.
