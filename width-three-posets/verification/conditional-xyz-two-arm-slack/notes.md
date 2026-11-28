# Longer two-arm tails and a crossed gate

This note extends the [conditional-XYZ two-arm result](../conditional-xyz-two-arm/notes.md). It uses that note's branch-order-preserving swap, rank pooling, and conditional XYZ lemma. The conclusions below are written mathematics, not checked in Lean. The full width-three conjecture remains open.

## Setting and dependencies

Let $P$ be a finite poset. For incomparable $a,b$, assume every strict predecessor of $a$ is below $b$. Put $S=\{b\}\cup(U(b)\setminus U(a))$, with $U$ the strict upset, and assume $p=\Pr(a<b)\le1/2$. Probabilities refer to uniformly random linear extensions of $P$. A balanced pair has comparison probability in $[1/3,2/3]$. Every $z\in S$ is incomparable with $a$; in particular the absence of a balanced pair implies $p<1/3$ and makes each $z\in S$ either low ($F(z)=\Pr(a<z)<1/3$) or high ($F(z)>2/3$). An earlier point of $S$ cannot be high while a poset successor is low.

Assume $S$ is the ordinal sum of a chain of $h\ge2$ vertices, starting at $b$ and ending at $q$, and a tail partitioned into two chains $X,Y$. Cross relations in the tail are allowed. Either arm may be empty, in which case $S$ is a chain and the claim below is immediate from rank pooling; the two-tail statements otherwise assume nonempty arms.

Here are the exact two tools from the earlier note, with ranks $\rho_R$ starting at one in any induced branch order $R$.

* **Rank pooling.** If $\rho_R(z)\le\rho_R(u)+\rho_R(v)$ for every $R$, then $F(z)\le F(u)+F(v)$. In particular this allows repeated anchors $u=v$. This follows by pooling cumulative prefixes of the nonincreasing cut histogram in each $R$, whose antitonicity is supplied by the swap.
* **Conditional XYZ.** If $w$ is low and $w<x,w<y$ in $S$, and
  $2\min(\rho_R(x),\rho_R(y))\le3\rho_R(w)$ for every $R$, then $x,y$ cannot both be high. Indeed, antitone prefix averages bound $\Pr(a<x,a<y)\le(3/2)F(w)$. Write $s=F(w)$, $u=\Pr(x<a)$, $v=\Pr(y<a)$. Conditioning the extension on $w<a$, the conditional XYZ inequality gives
  \[
    uv\le(1-s)\bigl(u+v-1+\Pr(a<x,a<y)\bigr).
  \]
  If $u,v<1/3$, increasing each to $1/3$ increases the right-minus-left expression strictly, so
  \[
    1/9 < (1-s)\bigl(\Pr(a<x,a<y)-1/3\bigr).
  \]
  This is incompatible with $s<1/3$ and the upper bound $(3/2)s$, since
  \[
    1/9-(1-s)((3/2)s-1/3)=(1/3-s)(4/3-(3/2)s)>0.
  \]
  Conditioning is legitimate because it gives the uniform law of the partial order with $w<a$ adjoined. The probability denominators are positive.

The prior swap also gives $\Pr(S<a)\le p$, meaning that the final cut has probability no greater than the initial cut. The initial chain must be entirely low under no balance, since the point at rank $i\ge2$ has rank no more than $2(i-1)$ and the first point $b$ is low.

## Generalized slack condition

**Theorem 1.** Suppose $h\ge2$, the two nonempty arms have lengths $r,t\le h+k$ for an integer $k\ge1$, and
\[
    \lfloor h/2\rfloor > \max(k,2k-2).
\]
Then $P$ has a balanced pair. This uses the original hypothesis $p\le1/2$, with no tighter numerical cap on $p$. In particular, $h\ge6$ allows both arms up to $h+2$, and $h\ge4k-2$ works for every $k\ge2$.

**Proof.** Write $i,j$ for the lengths of the low prefixes of $X,Y$. If both ends are low, every extension either puts $a$ before at least one of them or places all of $S$ before $a$. This would bound probability one above by the sum of two low comparison probabilities and the final-cut probability, strictly less than $1$.

Suppose $X$ has a first high vertex (one-based label $x_{i+1}$). In every induced branch order its rank is at most $h+i+t+1$: only the first $i$ vertices of $X$, some of $Y$, and the shared prefix can precede it. As low anchors take the last low in each arm, substituting $q$ for an empty low prefix. The earlier anchor has rank at least $h+\min(i,j)$; the later has rank at least $h+i+j$, because both low prefixes have then appeared. This is also valid for two empty low prefixes with the repeated anchor $q$. Hence $t-j\le h+\min(i,j)-1$ would imply rank domination of the high vertex by two low anchors, contradicting rank pooling. We have proved
\[
    t-j\ge h+\min(i,j).
\]
With $X,Y$ reversed, existence of a first high in $Y$ similarly forces $r-i\ge h+\min(i,j)$. If only one arm had a high vertex, the entire other arm would be low and its excess length would be zero, contrary to the first inequality or its symmetric counterpart. Thus both first high vertices exist and both inequalities hold.

The earlier of the two first high vertices has rank at most $h+i+j+1$, since only the common chain prefix and some of the two low prefixes can precede it. Both high vertices are strict successors of the low $q$ of fixed rank $h$. Conditional XYZ now rules out $2(i+j+1)\le h$ (which would give $2(h+i+j+1)\le3h$). Thus
\[
    i+j\ge\lfloor h/2\rfloor.
\]
On the other hand $r,t\le h+k$ and the two tail inequalities give $i,j\le k-\min(i,j)$. If one of $i,j$ is zero their sum is at most $k$; if both are positive, their sum is at most $2k-2$. This contradicts the hypothesis.

When one arm is empty, the whole branch is a chain. Repeated-anchor pooling makes every branch point low, and its final point plus the final cut accounts for probability one, contradiction. This handles the optional degenerate case independently of $k$.

## A genuinely crossed tail

**Theorem 2.** Let $h\ge2$, $k\ge2$, and index the two nonempty tail chains from zero, $x_0<\cdots<x_{r-1}$ and $y_0<\cdots<y_{t-1}$. Require
\[
    3\le r\le h+k,\quad 2\le t\le h+k,\qquad x_0<y_1,\qquad y_0<x_\ell
    \quad\text{for some }2\le\ell\le\min(h+1,r-1).
\]
Additional cross relations are allowed. If $\lfloor(h+3)/2\rfloor>2k-2$, then there is a balanced pair. In particular $h\ge3$ permits both arms up to $h+2$ under these crossed-gate hypotheses.

**Proof.** The cross relation $x_0<y_1$ leaves only $y_0$ as a possible tail point preceding $x_0$, giving $\rho_R(x_0)\le h+2\le2h=2\rho_R(q)$ in every $R$. Thus $x_0$ is low. Likewise $y_0<x_\ell$ leaves at most the $\ell$ points $x_0,\ldots,x_{\ell-1}$ as possible other-arm predecessors in an induced order. Hence
\[
    \rho_R(y_0)\le h+\ell+1\le2(h+1)\le2\rho_R(x_0),
\]
making $y_0$ low by rank pooling. The low-prefix sizes $i,j$ are now at least one. The argument in Theorem 1, which did not need the slack inequality to derive the tail constraints, gives both first high vertices and $i+j\le2k-2$.

Both first high vertices are strict successors of the low $x_0$ because they occur at positive arm indices and $x_0<y_1$. Their earlier rank is at most $h+i+j+1$ as before, but $\rho_R(x_0)\ge h+1$ for every $R$. Conditional XYZ rules out $2(h+i+j+1)\le3(h+1)$, giving
\[
    i+j\ge\lfloor(h+3)/2\rfloor.
\]
This contradicts the bound $2k-2$.

### An explicit 5+5 example, and why the pooled-rank method stalls

Take a prefix $b<c<q$ and append the ordinal sum with two arms of length $5$. Take the transitive closure of the arm orders, all comparisons placing the prefix below both arms, and just two additional comparisons $x_0<y_1$ and $y_0<x_2$. The only additional cross comparisons forced within the tail are $x_0<y_j$ for $j\ge1$ and $y_0<x_i$ for $i\ge2$: none of these chains of comparabilities implies $x_1<y_0$ or $y_0<x_1$. In particular the first two gates do not both precede all remaining tail vertices. This is not a double layer followed by two arms. The longest ordinal chain prefix is exactly three, since $x_0,y_0$ are incomparable and are both minimal in the tail. The original $h+1$ cap cannot cover ten tail points, under any partition into two arms. Theorem 1 also does not apply here ($\lfloor3/2\rfloor=1$); Theorem 2 applies at $h=3,k=2,\ell=2$.

For an actual width-three poset realizing this branch shape, adjoin one isolated point $a$. Its strict predecessor set is empty, and $S$ is the branch defined above. This poset has width exactly three: $S$ is covered by two chains and $\{a,x_0,y_0\}$ is an antichain. In this simple realization $p=1/14$, because the 13-element branch starts at $b$ in every extension and $a$ has 14 equally likely insertion cuts under each branch order. The theorem stands for arbitrary ambient $P$ realizing the shape, not just this easy isolated realization.

The two initially low extra anchors are $x_0,y_0$, in addition to the prefix. The static pooled-rank rule cannot move past this seed set in the example. To see this on actual induced orders, write the three-point prefix first and consider each of the following suffixes with either order of the initial two gates $x_0,y_0$:
\[
  (x_0,y_0),\ y_1,y_2,y_3,y_4,x_1,x_2,x_3,x_4,
  \qquad
  (x_0,y_0),\ x_1,x_2,x_3,x_4,y_1,y_2,y_3,y_4 .
\]
All four orders meet the two cross relations; both gate orders are permitted. In the first type $\rho(x_1)=10$, and in the second $\rho(y_1)=10$. Distinct seed anchors have rank sum at most $4+5=9$. The only repeated anchor that could reach rank 10 in one such witness is the gate at rank 5; place that gate first instead, at rank 4. Thus neither $x_1$ nor $y_1$, and consequently no later point of either arm, satisfies the pooled-rank domination criterion for any fixed pair of seed anchors. Conditional XYZ does make progress: $x_0$ is a common low predecessor of $x_1,y_1$, its rank is at least 4, and the earlier of $x_1,y_1$ has rank at most 6. This is precisely the factor-$3/2$ condition.

The accompanying Python check enumerates the 175 branch orders of this example and confirms these exact rank claims. The displayed witness orders and proofs are independent of that diagnostic.

## Scope

Both statements are restricted sufficient conditions for the good-pair approach, not proofs for all width-three posets. The conditional correlation uses L. A. Shepp, *The XYZ Conjecture and the FKG Inequality*, Ann. Probab. 10 (1982), 824–827, [doi:10.1214/aop/1176993791](https://doi.org/10.1214/aop/1176993791). Neither new theorem has been Lean-checked.
