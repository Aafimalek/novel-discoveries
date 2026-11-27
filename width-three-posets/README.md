# The 1/3–2/3 conjecture in width three

**Working note.** The width-three case is not solved here. We prove an injection for the rank of an element among a possibly branching set of incomparable elements, and a sufficient condition that gives a balanced pair. No priority claim is made for these lemmas.

## A monotonicity lemma

Let $a,b$ be incomparable in a finite poset, and suppose every strict predecessor of $a$ is a strict predecessor of $b$. Write $U(x)$ for the strict successors of $x$ and set $S=\{b\}\cup(U(b)\setminus U(a))$. Every member of $S$ is incomparable with $a$: a successor of $b$ below $a$ would force $b<a$. Every extension places $b$ first among the elements of $S$.

Partition linear extensions according to the order they induce on $S$ and the number $i$ of members of $S$ preceding $a$. In each fixed induced order, the number in bin $i$ is nonincreasing in $i$.

**Proof.** In bin $i>0$, swap $a$ with the last member $s$ of $S$ before $a$. No intervening element $z$ lies below $a$, since each such predecessor lies before $b$. None lies above $a$ or below $s$ by the original order. If $z>s$, then $z>b$ and $z\notin U(a)$, so $z\in S$, contradicting the choice of $s$. Also $a$ and $s$ are incomparable. Thus the swap gives a linear extension. The induced order on $S$ is unchanged, and the new bin is $i-1$. The first member of $S$ after $a$ in the image is $s$, so the map is injective.

## A two-chain sufficient condition

In width three, $S$ has width at most two, since $a$ is incomparable with every member. Cover $S$ by disjoint chains $C,D$, with $b$ in $C$, using Dilworth's theorem. Put $p=\Pr(a<b)$ and $\eta=\Pr(\min D<a)$ for nonempty $D$ (otherwise $\eta=0$); probabilities are over uniform linear extensions. If $p+\eta\le1/3$, then some incomparable pair is balanced.

**Proof.** Write $C=\{b_1<\cdots<b_k\}$ with $b_1=b$. In the bin where exactly $i>0$ members of $C$ precede $a$, consider only extensions in which no member of $D$ precedes $a$. Repeatedly apply the swap in the first lemma until $a$ precedes $b_1$. This is an injection for each fixed $i$: the inverse applies $i$ swaps, each with the first member of $S$ after $a$. Hence the full bin has probability at most $p+\eta$. Its cumulative bin probabilities start at $p$ and end at $1$. If $p=1/3$, $a,b$ are balanced. Otherwise the first cumulative probability at least $1/3$ is at most $2/3$, since each step adds at most $1/3$. This cannot be the final bin at $1$. Each preceding cumulative probability is $\Pr(a<b_j)$ for some $j$, so one of these pairs is balanced.

## Forks and diamonds

Suppose $S$ is exactly the three-element fork $b<x,y$ or the four-element diamond $b<x,y<t$, with $x,y$ incomparable, and suppose $p\le5/18$. Then there is a balanced pair.

Let $q_i$ be the unconditional bin probabilities from the first lemma, so $q_0=p$, and put $A=q_0+q_1$. This is the probability that $a$ precedes both $x$ and $y$. Monotonicity gives $A\ge 2/(|S|+1)\ge 2/5$. If there is no balanced pair, then both $\Pr(a<x)$ and $\Pr(a<y)$ exceed $2/3$. Also one order of $x,y$, say $y<x$, has probability less than $1/3$. In that induced order of $S$, the joint probability of bin 2 is at most one third of the order's total probability, since bins 0 and 1 each have at least as much mass. Hence $\Pr(y<a<x)<1/9$. But $\Pr(a<x)=A+\Pr(y<a<x)<2p+1/9\le2/3$, a contradiction.

The remaining obstacle is controlling $\eta$ or replacing it with a smaller, bin-specific bound. Monotonicity alone does not give the conjecture, since the order of incomparable members of $S$ can vary across extensions.

- [Zaguia's chain argument](https://arxiv.org/abs/1610.00809)
- [Aires, Chan, Pak and Panova on the general bound](https://arxiv.org/abs/2609.30888)
- [Gupta's census through fourteen elements](https://arxiv.org/abs/2607.23926)

Aafi Khan Malek selected and directed this project. ChatGPT assisted with literature and proof development. Codex was not used. The conditional swap injection and the fork/diamond result are checked in Lean 4.36.0. See [`WidthThree.forkDiamond_balanced`](lean/ForkDiamond.lean), with only `propext`, `Classical.choice`, and `Quot.sound` reported by `#print axioms`. The theorem assumes the stated upset shape and threshold; it does not settle the width-three conjecture.

[Exact small-instance check](verification/check.mjs): run `node width-three-posets/verification/check.mjs` from the repository root. The script enumerates linear extensions on five elements and checks conditional monotonicity; it does not prove the conjecture.

## Extension to layered exclusive upsets

Suppose the same $S$ is an ordinal sum of singleton or two-element antichain layers, starting with $\{b\}$. Assume $p=\Pr(a<b)\le1/2$. Then a balanced pair exists if $S$ has no second layer, if its second layer is a singleton, or if $p\le5/18$.

Assume no pair is balanced. Thus $p<1/3$. Write $q_i$ for the probability exactly $i$ members of $S$ precede $a$, and $m=|S|$. The earlier injection gives $p=q_0\ge q_1\ge\cdots\ge q_m$. For a singleton at rank $r$ within $S$, its $a$-before probability is $\sum_{i<r}q_i$. For a double layer ending at rank $r$, the mean of its two probabilities is $\sum_{i<r-1}q_i+q_{r-1}/2$. The individual probabilities differ by at most $q_{r-1}\le p<1/3$, so each layer is entirely below $1/3$ or entirely above $2/3$.

The first layer is low and the last cannot be low. If the last is a singleton, its probability is $1-q_m\ge1-p$. Otherwise $m\ge3$ and both probabilities are at least $1-q_{m-1}-q_m\ge1-2/(m+1)\ge1/2$, by monotonicity. A low singleton of rank $r\ge2$ has $q_r<1/(3r)$, so the next layer's mean rises by at most $3q_r/2<1/3$. A low double ending at rank $r\ge3$ has $q_{r-1}<1/[3(r-1/2)]$, so the next mean rises by at most $2q_{r-1}<1/3$. From $b$ to a singleton the jump is at most $q_1\le p$. Thus the sole possible transition from low to high is from $b$ directly to a double layer at ranks 2 and 3.

For that double layer, label its members $x,y$ so that $y<x$ is the minority order, of probability less than $1/3$. Within this order, bin 2 has at most a third of its probability: conditional monotonicity applies after fixing, or averaging over, the rest of the induced order of $S$. Hence $\Pr(a<x)<q_0+q_1+1/9\le2p+1/9$. This cannot be high if $p\le5/18$, a contradiction.

This adds an infinite class of configurations with repeated branching. It does not remove the layered-order hypothesis. It is a written proof, not a Lean formalization.

## A checked rank-reachability criterion

[`balanced_of_branchRankReach`](lean/ForkDiamond.lean) gives a balanced pair when the starting vertex reaches two vertices whose downsets cover the exclusive upset. A step from x to y is allowed when the number of upset vertices that are not strict successors of y is at most twice the number at or below x. The criterion can apply to nonlayered upsets but does not cover all width-three posets. Lean reports only the standard three axioms.

The theorem [`balanced_of_singletonHeadLayers`](lean/ForkDiamond.lean) checks the layered sufficient condition when the second layer is a singleton. It derives the doubling comparisons from the actual ordinal layers. This does not cover arbitrary width-three upsets or a general two-element second layer.

### Two-element second layer in Lean

[`LayeredSecondDouble.lean`](lean/LayeredSecondDouble.lean) extends the checked sufficient condition to an exclusive upset that is an ordinal sum of nonempty layers of size one or two, including arbitrarily many later layers when the second layer has two elements and the required initial probability is at most (5/18). For a singleton second layer the earlier threshold is (1/2). The final theorem `WidthThree.balanced_of_layeredBranch` checks both alternatives with only standard Lean axioms. Arbitrary width-three posets need not have this shape and remain outside the theorem.

The same module also proves `balanced_of_frontForkRankReach` and `balanced_of_frontForkSmallSeed` for a common upper tail that need not be layered. They use low rank seeds and certified rank-step reachability; an immediate fork into two interleaving long chains still falls outside this sufficient condition.
