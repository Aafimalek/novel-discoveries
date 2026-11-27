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

Aafi Khan Malek selected and directed this project. ChatGPT assisted with literature and proof development. Codex was not used. The stated co-triple theorem is formalized in [`lean/CoTriple.lean`](lean/CoTriple.lean) as `FranklHeightSix.fullNonemptyCoTriple_majority`. It was checked with Lean 4.36.0, and `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`. The separate structural reduction below is not covered by that verification.

[Exact arithmetic check](verification/check.mjs): run `node frankl-height-six/verification/check.mjs` from the repository root. The script checks the small cases in the polynomial calculation, not the full proof.

## A structural reduction without the co-triple assumption

In a minimal counterexample to the strict-half assertion for families of nonempty sets at height at most six, the domination order has no chain of three points. Every dominated point has its co-singleton present, and two distinct undominated points share at most one dominated point.

To see this, take a counterexample with the fewest members and then smallest ground set $U$ (of size $n$). The minimality arguments of the [height-five manuscript, Lemma 1.1](https://we-solve.github.io/contributions/frankl-s-union-closed-sets-conjecture-964c25bb/attempt-3/r1/) apply: removing a minimal member or deleting a twin cannot increase height. For the latter, deletion reflects inclusion because the surviving twin records membership of the deleted point. Thus the family is separating, has even size $2t$, and has at least three points of frequency $t$. Such points are undominated: strict domination would otherwise force the same frequency and identical membership. Here $s$ dominates $v$ when every member containing $v$ also contains $s$.

For each point $v$ let $C_v$ be the largest member avoiding $v$. These exist by union closure and the half-frequency bound, and are distinct by separation. For distinct undominated $s,s'$, the members $U$ and $C_v$ for $v$ outside the pair all contain both, so at least $n-1$ members contain both. At least as many avoid both, by inclusion–exclusion and the half-frequency bound. Their maximum $T$ cannot start an ascending chain of five members: its avoiding fiber would then have height at most two and size at most $|T|+1\le n-3$, by the height-two argument above. Since $T\subsetneq C_s\subsetneq U$, every $C_s$ for an undominated $s$ starts chains of length at most three.

In the intersection-closed complement family, $K_v=U\setminus C_v$ consists of $v$ and every point it dominates. It is the intersection of all complements containing $v$. Thus $K_s$ for an undominated $s$ has inclusion rank at most three, counting the empty set. A domination chain $s>q>p$ with $s$ maximal would imply $\varnothing\subsetneq K_p\subsetneq K_q\subsetneq K_s$, which is impossible. A dominated point $p$ therefore dominates no other point, so $K_p=\{p\}$. If two distinct undominated points $s,s'$ shared dominated points $p,q$, the chain $\varnothing\subsetneq K_p\subsetneq K_s\cap K_{s'}\subsetneq K_s$ would again have four members.

What remains: a minimal counterexample may still have a two-level domination order or may omit many co-pairs, so this reduction does not solve height six.

## Checked structure without the co-triple hypothesis

[`FranklStructural.lean`](lean/FranklStructural.lean) formalizes some independent reductions for the usual **at least half** conclusion. A ground-minimal counterexample is singleton-free and twin-free, and every active point has a canonical pair of members differing exactly by that point. The height-six restriction is preserved under coordinate erasure. These checked statements depend only on the standard three Lean axioms. They do not prove the unrestricted conjecture or every part of the earlier written structural note.

The same file proves a minimum-ground reduction exists, that every forcing principal ideal and that ideal minus its generator appear as complements, and that a strict forcing chain of six points is impossible. The stronger claim that no three-point forcing chain occurs is not asserted by this formalization.

[`FranklNoThreeForcing.lean`](lean/FranklNoThreeForcing.lean) strengthens this to a checked reduction to **no three-point forcing chain** for a separating family. Every height-six counterexample to strict majority of nonempty sets has a separating, three-chain-free counterexample, without parity or exact-half assumptions. This includes the corresponding reduction for the usual at-least-half conjecture. The reduction does not rule out the remaining counterexamples.

### Forcing stars and avoidance fibers in Lean

[`FranklForcingFiber.lean`](lean/FranklForcingFiber.lean) gives a stronger structural reduction allowing exact-half frequencies. Any hypothetical height-six counterexample has a separating ground-minimal reduction in which the proper forcing relation consists of disjoint outward stars and isolated points. Each leaf's largest avoiding member omits exactly the leaf and its parent. Inside a fiber avoiding one star's leaf, the source and leaves in every other star have identical incidence. These are restrictions on a possible counterexample, not a proof of the conjecture. The declarations compile in Lean 4.36 with only `propext`, `Classical.choice`, and `Quot.sound`.

### Pair-fiber counting and the necessity of an isolated point

[The proof note](star-counting.md) records the next checked reductions. In a ground-minimal counterexample, **at least one point is isolated in the proper-forcing graph**. Projecting onto all leaves otherwise preserves the frequency and height bounds while reducing the ground. With at least two nontrivial stars, Lean also checks the leaf bound and a strengthened pair-fiber counting disjunction. If any of those stars has two or more leaves, there must be at least three isolated points, and the ground size is at most two plus the isolated-point count plus its number of pairs. The unrestricted height-six case remains open.
