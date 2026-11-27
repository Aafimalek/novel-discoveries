# Frankl's conjecture at height six

**Working note.** A restricted case is proved below. The unrestricted height-six case is not solved here. No priority claim is made.

Let a union-closed family $\mathcal F$ consist of nonempty subsets of a nonempty ground set $U$, and define height as the largest number of members in a strict inclusion chain. Suppose the height is at most six, and suppose $U\setminus S$ belongs to $\mathcal F$ for every $S\subseteq U$ of size at most three with $U\setminus S\ne\varnothing$. Then some point belongs to strictly more than half of the members.

## Proof

Set $n=|U|$ and $t=|\mathcal F|/2$. For $n\le4$ each point lies in $2^{n-1}$ of the required sets, while $\mathcal F$ has at most $2^n-1$ members. Assume $n\ge5$, and, for contradiction, every point occurs at most $t$ times. Call a set shallow if its complement has size at most three. Each point is in $X=\sum_{j=0}^3\binom{n-1}{j}$ shallow sets and absent from $Y=\sum_{j=0}^2\binom{n-1}{j}$ shallow sets. Put $A=X-Y=\binom{n-1}{3}>0$ and $y=t-X\ge0$. The number of nonshallow members is $D=2t-X-Y=A+2y$. Each point is absent from at least $t-Y=A+y$ nonshallow members, so their mean complement size is at least $a=n(A+y)/D=n/2+nA/(2D)$.

Fix four points $T$. The members avoiding $T$ form a union-closed fiber. If nonempty, let $W$ be its maximum. Any chain ending at $W$ extends by four strict steps: successively take the complements in $U$ of a three-element, two-element, one-element and empty subset of $T$, nested in that order. Thus the fiber has height at most two. Any two distinct proper members of the fiber have union $W$: otherwise either they are comparable, giving a three-member chain including $W$, or their union gives such a chain. Their nonempty complements in $W$ are therefore pairwise disjoint, so the fiber has at most $|W|+1\le n-3$ members.

Counting incidences of quadruples in nonshallow complements gives
$D\binom{a}{4}\le\binom{n}{4}(n-3)$ by Jensen's inequality. Here $x\mapsto x(x-1)(x-2)(x-3)/24$ is increasing and convex on $[4,\infty)$. We have $a>n/2\ge4$ for $n\ge8$. For $n=5,6,7$ use $D\le 2^n-1-\sum_{j=0}^3\binom nj$ to obtain respectively $a\ge9/2,\ 31/7,\ 83/18$, all above four. Substituting $D=nA/(2a-n)$ and $nA=4\binom{n}{4}$ gives
\[
 P_n(a):=a(a-1)(a-2)(a-3)-6(n-3)(2a-n)\le0.
\]

For $n\ge9$, $P_n(n/2)>0$ and $P_n'(n/2)=n^2(n-9)/2-n+30>0$. Since $P_n''(a)=12a^2-36a+22>0$ for $a\ge4$, this is a contradiction. For $n=8$ and $d=a-4\ge0$, $P_8(a)\ge24-10d+35d^2>0$: the quadratic has negative discriminant. For $n=7$, $P_7(4)=0$ and $P_7'(4)=2>0$; for $n=6$ and $n=5$ respectively the lower endpoints give $P_6(31/7)=3000/2401>0$ and $P_5(9/2)=177/16>0$, with derivatives already positive at four. Each case contradicts the incidence bound.

## What remains

A crucial next step is to remove the assumption that every complement of a triple is present, or to show that minimal counterexamples necessarily satisfy stronger structural conditions. The October [height-five manuscript](https://we-solve.github.io/contributions/frankl-s-union-closed-sets-conjecture-964c25bb/attempt-3/r1/) is a claimed result, not a peer-reviewed source. This note adapts its full-pair counting argument and does not depend on the manuscript's full theorem. See also [Tian's height-four preprint](https://arxiv.org/abs/2608.25147).

Aafi Khan Malek selected and directed this project. ChatGPT assisted with literature and proof development. Codex was not used. This working note has not been formalized in Lean.

[Exact arithmetic check](verification/check.mjs): run `node frankl-height-six/verification/check.mjs` from the repository root. The script checks the small cases in the polynomial calculation, not the full proof.
