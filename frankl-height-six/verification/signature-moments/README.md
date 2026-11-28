# A stronger one-isolate forcing-star bound

Aafi Khan Malek, independent researcher, Ahmedabad, India · [aafimalek2032@gmail.com](mailto:aafimalek2032@gmail.com)

Consider the ground-minimal weak height-six counterexample model from the [previous pair-block proof](../../star-counting.md). With exactly one isolated point and at least one forcing edge, that work verifies at least 14 stars and shows every star has one leaf. The argument below and the exact integer replay exclude counts 14–29, so **at least 30 forcing stars** (at least 61 ground points) are necessary in this case. They do not settle height six, other isolate counts, or larger numbers of stars. The new Sauer inequality for the **actual pair-avoidance fiber** is checked in Lean; the full count exclusion is not yet a Lean theorem.

[Paper PDF](paper/one-isolate-signature-moments.pdf) · [TeX source](paper/one-isolate-signature-moments.tex)

## 1. Signature Sauer and link caps

Write $k$ for the number of star centers. Every pair of centers lies in exactly one omitted-star block, and two different blocks meet in at most one point. For a pair $p,q$ in block $B$, write $W(p,q)$ for the number of blocks avoiding both. Its two-leaf avoidance fiber has at least $3k+W(p,q)$ members, as in the previous proof.

Fix $B$ of size $b$ with $h=k-b$ outsiders. Join outsiders $u,v$ if their unique block meets $B$, and let $E(B)$ count the link edges. Endpoints of each link have identical occurrence signatures in the compressed two-leaf fiber by the earlier closure lemma. Membership is constant within each component. Keeping one coordinate per component and the isolate is injective on this family, reflects inclusion, and preserves unions. The image remains union-closed of height at most three. If there are $c_B$ components, the height-three Sauer bound gives
$$
3k+W(p,q)\le H(c_B+1),\qquad H(n)=1+n+\binom n2 .
$$
Lean proves the bound using the number of distinct occurrence signatures; this is no larger than $c_B$.

If every block has size at most $r$, incidence counting gives
$$
W(p,q)\ge \left\lceil (k-2)d/r\right\rceil,\qquad
d=\max\left(0,\left\lceil\frac{k-3-2(r-2)}{r-1}\right\rceil\right).
$$
An outsider has $k-3$ other outsiders; its blocks through $p$ and $q$ cover at most $2(r-2)$ of these partners, so it is on at least $d$ blocks avoiding both.

A lower bound $w$ for some pair in $B$ gives $H(c_B+1)\ge 3k+w$. Let $c$ be the resulting lower bound on $c_B$. If $c>h$ the block is impossible. Otherwise $E(B)\le e=\binom{h-c+1}{2}$, since concentrating the excess component sizes in one component maximizes the possible clique edges. If the link edges contributed at each $a\in B$ number $E_a$, the outsider groups through $a$ have count at least $h-E_a$. Choose $p,q$ so the total $E_a$ at the remaining $b-2$ points is at most $\lfloor(b-2)E(B)/b\rfloor$. Other blocks avoiding $p,q$ must cover the outside pairs not in the link graph. Hence a new lower bound is
$$
(b-2)h-\left\lfloor (b-2)e/b\right\rfloor+
\left\lceil\frac{\binom h2-e}{\binom r2}\right\rceil.
$$
Repeat when the lower bound improves. Each round only needs to apply to some pair in $B$, since the link graph is fixed by $B$. This gives an edge cap $L_b$ or rules out the block size.

## 2. Feed the block counts back into the caps

Let $n_s$ count size-$s$ blocks for $s\ge3$, let $\kappa_s=\binom{s}{2}-1$, and put $\sigma=\sum_s n_s\kappa_s$. Count the $\binom{k-2}{2}$ pairs outside $p,q$ for $p,q\in B$. A block avoiding them contributes one plus its saving $\binom{s}{2}-1$. Every other block except $B$ touches only one of $p,q$ and contributes at most its saving, since $\binom{s-1}{2}\le\binom{s}{2}-1$. The selected block contributes exactly $\binom{b-2}{2}$. Thus
$$
W(p,q)\ge\binom{k-2}{2}-\binom{b-2}{2}+\kappa_b-\sigma.
$$
Use this in the cap iteration. The largest size $r$ is bounded initially by $H(k+1-r)\ge3k$. Also $\sigma\le\left\lfloor\binom{k}{2}\kappa_r/\binom{r}{2}\right\rfloor$ because saving per covered pair is nondecreasing with size. The cap must use the candidate value of $\sigma$, not just a worst-case saving. The count vectors satisfy $\sum_s n_s\binom{s}{2}\le\binom{k}{2}$.

## 3. Weighted degree moment

For a chosen subset $J$ of the nonpair block sizes, put $\alpha_s=\binom{s-1}{2}$ and $d_v=\sum_{B\ni v,\,|B|\in J}\alpha_{|B|}$. When distinct blocks $A,C$ intersect, the second contributes exactly $\alpha_{|C|}$ link edges to the first. Expanding the sum of degree squares therefore gives the diagonal term plus the weighted intersecting ordered pairs. Dropping blocks not in $J$ can only lower the measured link counts. In particular,
$$
D_J=\sum_v d_v=\sum_{s\in J}s\alpha_s n_s,\qquad
\sum_v d_v^2\le U_J=\sum_{s\in J}n_s(s\alpha_s^2+\alpha_s L_s).
$$
The least possible sum of squares of nonnegative integer scores with this total is obtained by scores differing by at most one: move one unit from $a$ to $b$ whenever $a\ge b+2$. If that minimum exceeds $U_J$, rule out the count vector.

A shortcut can exclude an entire $(r,\sigma)$ row. For the full size collection put $d_s=s\alpha_s$, $u_s=s\alpha_s^2+\alpha_s L_s$. Cauchy–Schwarz and a square give $0\ge D^2-kU\ge 2zD-z^2-kU$ for any integer $z$. Separate one size-$r$ block. The remaining saving is $\sigma-\kappa_r$; every remaining size-$s$ block contributes $(2zd_s-ku_s)/\kappa_s$ per unit of saving. An exact certificate for this whole row is that, for every admissible $s$,
$$
(2zd_r-ku_r-z^2)\kappa_s+(\sigma-\kappa_r)(2zd_s-ku_s)>0.
$$
The search chooses candidate $z$ near exact rational stationary points and line intersections. Each reported rejection tests the integer inequalities; any row without a certificate goes to explicit count enumeration.

## 4. Pair deficits and optional support restriction

Let $M=\binom{k}{2}-\sum_s n_s\binom{s}{2}$ be the number of size-two blocks. In a selected block $B$ of size $b$, each vertex has $k-b$ partner pairs leading outside. A different block of size $s\ge3$ through that vertex consumes $s-1$ of these pairs and contributes $\alpha_s$ links. The total number of size-two incidences at the vertices of $B$ is at most $M$, since no size-two block can have both endpoints in $B$. A finite unbounded knapsack on length $s-1$ and cost $\alpha_s$ gives a lower bound on the link contribution of a vertex at each local deficit. Combining the $b$ vertices at total deficit at most $M$ gives a lower bound for $E(B)$. This forgets realizability of the degree profiles, which is safe for a lower bound.

The checker additionally permits a support restriction. For $n$ blocks of one size $s$ with $I$ intersecting unordered pairs, their union has at least $sn-I$ vertices, and $I\le n\lfloor L_s/\alpha_s\rfloor/2$. Deleting this union loses at most $nL_s-2I\alpha_s$ of the other blocks' weighted degree, since internal intersections already consume that link budget. Independently a block of size $t$ can lose at most $\min(t,\lfloor L_t/\alpha_s\rfloor)$ vertices, charging $\alpha_s$ per removed block it intersects. Apply the moment on the remaining support. A removed occurrence in size $t$ loses at most $t-1=2\alpha_t/(t-2)$ covered pairs, giving an outside pair capacity test. The checker tests every possible $I$.

## Reproduction and Lean scope

- Run **python3 replay_combined.py 14 29 --require-none**. The complete output is in replay-results.txt. This is exact integer arithmetic with no external solver.
- Build FranklSignatureHeightThree.lean after the earlier FranklHeightThreeSauer module, and then FranklPairSignatureSauer.lean after FranklBlockClosureEncoding. Both passed with Lean 4.36.0 and Mathlib pin fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The actual fiber theorem pair_fiber_card_le_sauer_block_signatures uses only propext, Classical.choice and Quot.sound.
- The new forcing-star lower bound is a written proof with a finite arithmetic replay, not yet an end-to-end Lean result. The earlier fully Lean-verified numerical lower bound remains 14.

ChatGPT assisted with proof development, formalization and writing. Codex was not used.
