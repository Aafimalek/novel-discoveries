# Diagonal-gated two-arm branches

This is a **written structural application** of the Lean-checked actual-ranking
theorem `WidthThree.jointComparisonFrequency_of_branchRankSum`. It gives
unbounded intertwined examples which the earlier opposite-arm degree
condition misses. The geometry-to-rank proof below is not Lean-checked, and
this is not a result for all width-three posets.

## Setting and precise statement

Let $P$ be a finite poset. Take incomparable $a,b$ such that each strict
predecessor of $a$ is strictly below $b$. Write $U$ for strict upset and
$S=\{b\}\cup(U(b)\setminus U(a))$. Assume
$p=\Pr(a<b)\le 1/2$ in the uniform distribution on all linear extensions of
$P$. A balanced pair has comparison probability in $[1/3,2/3]$.

Suppose $S$ is the ordinal sum of an $h$-point chain, $h\ge2$, from $b$
to $q$, and a tail partitioned into chains
$x_0<\cdots<x_{r-1}$ and $y_0<\cdots<y_{t-1}$. For nonnegative integers
$d,e$, require the diagonal gates
$$
 x_k<y_{k+d},\qquad y_k<x_{k+e}
$$
whenever both endpoints of the corresponding gate exist. There is no
restriction on $r,t$, they need not be equal, and additional cross relations
are permitted. Empty arms are allowed. If $d=e=0$ and both arms are nonempty,
the gate hypotheses are inconsistent; no such vacuous case is needed.

**Theorem A (rank pooling only).** If $D=\max(d,e)\le 2h-2$, $P$ has a
balanced pair.

In fact, if $D\le2h-1$, the only possible no-balance case would have each
arm's first point high, i.e. both $\Pr(a<x_0),\Pr(a<y_0)>2/3$.
Below we also remove that case and extend the numerical range using the
separate written conditional XYZ argument.

## Exact dependence on the prior ranking results

Write $\rho_R(z)$ for the one-based rank of $z$ in $R$ restricted to
$S$, and $F(z)=\Pr(a<z)$, for $z\in S$. All these $z$ are incomparable
with $a$. Each actual ambient extension is counted once; induced orders
are not assumed equally likely, and no independence or product factorization
of the cut and induced order is used.

The existing branch-order swap gives
$\Pr(\text{all of }S\text{ before }a)\le p$, since cut counts are
nonincreasing within each fixed induced order. The existing single-target
pooling result `WidthThree.pairCount_le_add_of_pooledBranchPositions` gives
$F(z)\le F(u)+F(v)$ when $\rho_R(z)\le\rho_R(u)+\rho_R(v)$ for every
actual ranking $R$. This follows for probabilities by dividing counts by
the common positive number of extensions. The Lean-checked
`WidthThree.jointComparisonFrequency_of_branchRankSum` gives
$$
 F(x)+F(y)\le 2(F(u)+F(v))
 \quad\text{if}\quad
 \rho_R(x)+\rho_R(y)\le 2(\rho_R(u)+\rho_R(v))
 \quad\text{for every }R.
$$
Repeated anchors $u=v$ are allowed in both. For direct replay, the
companion ranking package has exact statements in
`JointBranchOrderDraft.lean` and typed audit in `JointBranchOrderAudit.lean`;
the unformalized step here is supplying the universal rank hypothesis from
the branch structure and threading the no-balance contradiction.

## Geometry-to-rank proof

Assume no pair is balanced. Thus $p<1/3$, and each $z\in S$ is low if
$F(z)<1/3$ or high if $F(z)>2/3$; these are the only possibilities.
Monotonicity of $F$ along poset chains makes low sets initial segments.
The initial $h$-point chain is low by induction: its fixed rank $k\ge2$
is at most twice its preceding rank $k-1$. If one arm is empty the whole
branch is a chain, so the same induction makes its maximum low. Its
comparison with $a$ and the final cut then partition all extensions, of
total probability at most $F(\max S)+p<1$, impossible. This also handles
both arms empty. From now on $r,t>0$.

Let $i,j$ be the low-prefix lengths on $X,Y$. Put $m=\max(i,j)$,
$s=\min(i,j)$, and $\Delta=|i-j|=m-s$. A last-low anchor on an arm is its
last low or $q$ when its low prefix is empty. Choose the following pair
$u,v$ of low anchors, **fixed independently of $R$**:

* If $s\ge\Delta$, use the two arms' respective last-low anchors.
  The earlier anchor has rank at least $h+s$. The later anchor has rank
  at least $h+i+j$, since by its position all $i+j$ lows of the two arms
  have appeared. This includes the case one anchor is $q$, and if
  $i=j=0$ both anchors are $q$ of rank $h$.
* If $\Delta>s$, repeat the last low of the longer low prefix; its rank
  is at least $h+m$. This arm is nonempty by $\Delta>0$.

Set $M=\max(s,\Delta)$. In both cases the selected anchors satisfy, in
every order,
$$
 A_R=\rho_R(u)+\rho_R(v)\ge 2h+i+j+M.                 \tag{1}
$$
In the second case use $2m=i+j+\Delta$. This choice is why one does not
lose slack when the two low prefixes are imbalanced.

Both arms have a first high. If all tail points are low, the two comparisons
of $a$ against their chain maxima, together with the final cut, cover all
extensions and have total probability $<1$. If exactly one arm has a high,
each point preceding its first high in any induced order belongs to the
common chain or one of the two low prefixes. Its rank is at most
$h+i+j+1\le A_R$, so single-target pooling contradicts high status.
Write the two first highs as $\alpha=x_i,\ \beta=y_j$. They are incomparable:
if $\alpha<\beta$, then all highs on the other arm succeed $\alpha$, so
again its rank is at most $h+i+j+1\le A_R$. The symmetric argument handles
$\beta<\alpha$.

Let $L_X$ count the high $X$-points incomparable with $\beta$, and let
$L_Y$ count the high $Y$-points incomparable with $\alpha$. In every
induced order the earlier high rank is at most $h+i+j+1$. If the later
head is $\beta$, its other possible earlier points are the at most $L_X$
high $X$-points incomparable with $\beta$: none can lie strictly below
$\beta$ in the poset, as that would imply $\alpha<\beta$. The symmetric
bound uses $L_Y$. Consequently,
$$
 \rho_R(\alpha)+\rho_R(\beta)
 \le 2h+2(i+j)+2+\max(L_X,L_Y).
$$
If $\max(L_X,L_Y)\le2h+2M-2$, the right side is at most $2A_R$ by
(1), uniformly for every actual $R$. Applying exactly the verified
frequency endpoint displayed above makes the two high probabilities
sum to at most twice the sum of two low probabilities, a contradiction.
Therefore
$$
 \max(L_X,L_Y)\ge2h+2M-1.                              \tag{2}
$$

Now use the gates (finite endpoints matter). By the $X$ chain,
$y_j<x_k$ for every existing $k\ge j+e$: if such $k$ exists, then
$x_{j+e}$ exists and has the required gate from $y_j$. Thus any counted
$k$ lies in $i\le k<j+e$. Similarly counted high $Y$-indices lie in
$j\le k<i+d$. Both ranges are nonempty because the first highs are
incomparable. With $\delta=i-j$ as a signed integer,
$$
 L_X\le e-\delta,\qquad L_Y\le d+\delta,
 \qquad \max(L_X,L_Y)\le D+\Delta.                    \tag{3}
$$
Truncation at $r,t$ only lowers these upper bounds. No exact description
of the cross comparabilities or restrictions on extra edges are needed.

Combining (2) and (3) gives the necessary condition
$$
 \boxed{D\ge 2h-1+2M-\Delta.}                         \tag{4}
$$
Since $2M-\Delta\ge0$, this proves Theorem A. The last term can vanish only
if $\Delta=0$ and $s=0$: indeed $2M-\Delta\ge\Delta$ and, if
$\Delta=0$, it equals $2s$. This proves the assertion at $D=2h-1$.

## Optional widening with conditional XYZ (separate dependency)

Use the written [conditional-XYZ two-arm argument](https://github.com/Aafimalek/novel-discoveries/tree/6add80bc727aef16d920be7ce39d8312fed99a87/width-three-posets/verification/conditional-xyz-two-arm-slack):
if $q$ is low, $q<x,y$, and
$2\min(\rho_R(x),\rho_R(y))\le 3\rho_R(q)$ in every order, then $x,y$
cannot both be high. This conditional XYZ step is **not** part of the
checked frequency theorem and is not claimed as Lean-checked.

Here the earlier high has rank at most $h+i+j+1$ and
$\rho_R(q)=h$. Therefore no balance entails
$2(i+j+1)>h$, or $2s+\Delta=i+j\ge K=\lfloor h/2\rfloor$.
The nonnegative integer $T=2M-\Delta$ always satisfies
$3T\ge2s+\Delta$: the difference is $4(s-\Delta)$ if $s\ge\Delta$,
and $2(\Delta-s)$ otherwise. Thus (4) requires
$D\ge2h-1+\lceil K/3\rceil$. In particular:

**Theorem B (with written conditional XYZ).** The same conclusion holds
if $D\le2h-2+\lceil\lfloor h/2\rfloor/3\rceil$.

## An actual longer intertwined width-three family

Take $h=2, r=t=n\ge3, d=e=2$, put in both gate families and the
arm orders, and take transitive closure. Every generating edge advances
the index, and the first cross edge on a path advances it by two. Thus
$$
 x_i<y_j\iff j\ge i+2,\qquad y_j<x_i\iff i\ge j+2.
$$
The reverse implications are the gate followed by the other arm order.
Consequently cross-arm incomparability is exactly $|i-j|\le1$. The
incomparability graph of the tail is connected (the diagonal links and
the adjacent links connect consecutive diagonal pairs), bipartite and
has a degree-three interior vertex for every $n\ge3$. Its only
bipartition up to swapping is the two arms, so repartition does not lower
the maximum cross-arm incomparability degree. Also the common ordinal
chain prefix really ends at two: the tail has two incomparable minimal
points $x_0,y_0$. Hence the earlier $2h-2=2$ local-degree criterion
cannot cover this family by repartitioning. The earlier crossed-gate
criterion with $x_0<y_1$, or its arm swap, does not apply either.
For comparison, $n=1,2$ has degree at most two, hence is not an example
of strict improvement; those cases are covered by Theorem A nonetheless.

No single-head rule from two initial low anchors can get started. Placing
$y_0,y_1$ then $x_0$ first in the tail is legal (validate all generators,
or take the three-element ideal and extend it); it gives
$\rho_R(x_0)=5>4=2\rho_R(q)$. The symmetric order does this for $y_0$.
But the earlier of these two heads is always at rank 3 and the later
has rank at most 5, so their sum is at most 8, just within joint pooling.
This is the genuine joint step at the empty-low-prefix corner.

Adjoining an isolated $a$ realizes an ambient poset of width exactly
three with the stipulated exclusive branch: two chains cover $S$,
and $a,x_0,y_0$ form an antichain. Exactly one of the $2+2n+1$
equally possible insertions of $a$, for each branch order, puts it
before $b$; thus $p=1/(2n+3)\le1/2$ in this explicit realization.
Theorems A and B apply also to other ambient posets with the stated
good pair and branch; they do not assume $a$ isolated.

The companion bounded exact audit checks the integer differences, cross
closure, uniqueness of the arm bipartition via connectivity, and the
small $n$ cases. Neither proof depends on this finite audit.
