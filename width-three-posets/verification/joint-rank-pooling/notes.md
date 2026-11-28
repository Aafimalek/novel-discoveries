# Joint rank pooling for intertwined two-arm branches

This note extends the [earlier two-arm slack argument](../conditional-xyz-slack/notes.md) in the 1/3–2/3 problem. Its new estimates use only antitone conditional cut histograms, not conditional XYZ. They are written mathematics, not new Lean theorems. The full width-three conjecture remains open.

## Setting and previously checked inputs

Let $P$ be a finite poset and let $a,b$ be incomparable, with every strict predecessor of $a$ strictly below $b$. Write $S=\{b\}\cup(U(b)\setminus U(a))$, where $U$ denotes the strict upset. Then every point of $S$ is incomparable with $a$. Assume $p=\Pr(a<b)\le1/2$ under the uniform linear-extension law. A balanced pair means a pair whose comparison probability belongs to $[1/3,2/3]$.

For each induced branch order $R$ on $S$, let $m_R(k)$ be the probability of that order and the cut with exactly $k$ points of $S$ before $a$. The earlier branch-swap injection, checked in Lean as WidthThree.natCard_binGiven_succ_le (module BranchOrder), makes $m_R(k)$ nonincreasing in $k$. Indeed, swap $a$ with the last branch point $z$ before it. Predecessors of $a$ are strictly below $b\le z$. Any successor of $z$ strictly between $z$ and $a$ in the extension would have to lie in $S$, which is impossible. The branch order is preserved and the swap is uniquely inverted on its image. In particular the final unconditional cut has probability at most the initial cut, $p$.

Let $\rho_R(z)$ be the one-based branch rank and $M_R(s)=\sum_{0\le k<s}m_R(k)$, truncated past the final cut. Thus $F(z)=\Pr(a<z)=\sum_R M_R(\rho_R(z))$. The already checked pooled-rank implication (WidthThree.pairCount_le_add_of_pooledBranchPositions) is
\[
 \bigl(\rho_R(z)\le\rho_R(u)+\rho_R(v)\text{ for every }R\bigr)
 \quad\Longrightarrow\quad F(z)\le F(u)+F(v).
\]
The reason is subadditivity of nonincreasing prefix sums, applied separately in each $R$. The same low anchor can be repeated. The new argument below is a different, two-target estimate; it does not need two separate pointwise single-target dominations.

## New lemma: joint rank pooling

If in every induced branch order
\[
 \rho_R(x)+\rho_R(y)\le 2\bigl(\rho_R(u)+\rho_R(v)\bigr),
\]
then
\[
 F(x)+F(y)\le2\bigl(F(u)+F(v)\bigr).
\]

To see this, fix an order and let its ranks for these points be $r,s,d,e$. Write $N=|S|$ and set $m_R(N+1)=0$. For $1\le H\le N+1$ put $w_H=m_R(H-1)-m_R(H)\ge0$. Telescoping for each cut and exchanging finite sums gives
\[
 M_R(k)=\sum_H w_H\min(k,H).
\]
For every $H$, we have
\[
 \min(r,H)+\min(s,H)\le2\bigl(\min(d,H)+\min(e,H)\bigr).
\]
If $H\le\max(d,e)$, one doubled anchor alone supplies $2H$, bounding the left side. If $H>\max(d,e)$, the right side is $2(d+e)\ge r+s$. Multiply by $w_H$, sum over $H$, and then sum over branch orders. This also applies when $u=v$.

## Necessary condition for a hypothetical no-balance two-arm branch

Suppose $S$ is the ordinal sum of a chain prefix of $h\ge2$ points starting at $b$ and ending at $q$, and two tail chains $x_1<\cdots<x_r$ and $y_1<\cdots<y_t$ (arbitrary cross relations are allowed). Suppose no pair is balanced. Then $p<1/3$, each branch point is low ($F<1/3$) or high ($F>2/3$), and each chain's lows form an initial segment. All common-prefix points are low: $b$ is low, and for any next rank $j\ge2$ along the common chain, $j\le2(j-1)$ allows repeated-anchor rank pooling. If a tail arm is empty, $S$ is itself a chain and the same reasoning makes all of $S$ low, contradicting $1=F(\max S)+\Pr(S<a)\le F(\max S)+p$. Hence assume now both arms are nonempty.

Let $i,j$ be the two low-prefix lengths. For the low anchors take $u=x_i$ when $i>0$ and $u=q$ otherwise, and $v=y_j$ when $j>0$ and $v=q$ otherwise. In any induced order the earlier anchor has rank at least $h+\min(i,j)$, and at the later anchor both low prefixes have appeared, so the later rank is at least $h+i+j$. If both prefixes are empty, $u=v=q$ and the two bounds simply give two copies of rank $h$. Thus
\[
 \rho_R(u)+\rho_R(v)\ge2h+i+j+\min(i,j).                    \tag{1}
\]

Both arms must have a high point. If neither does, their low extrema together with the final cut cover all extensions, contradicting $1\le F(x_r)+F(y_t)+p<1$. If just one arm has a first high point, all points that can precede it in the branch consist of the common prefix and the two low prefixes. Its rank is at most $h+i+j+1\le2h+i+j+\min(i,j)$, and (1) plus single-target pooling is impossible. So the first highs $\alpha=x_{i+1}$ and $\beta=y_{j+1}$ exist. They are incomparable: if $\alpha<\beta$, every high point of the other arm is a strict successor of $\alpha$; hence again only the common chain and the two low prefixes can precede $\alpha$, contradicting single-target pooling. Use the same argument if $\beta<\alpha$.

Define the *incomparable high stretches*
\[
 L_X=|\{x_k:k>i,\ x_k\parallel\beta\}|,\qquad
 L_Y=|\{y_k:k>j,\ y_k\parallel\alpha\}|.
\]
The earlier first-high rank is at most $h+i+j+1$ because no high point precedes the earlier first high. If the later first high is $\beta$, the only additional possible predecessors are from the high suffix of $X$. None of those can be a strict predecessor of $\beta$ in the poset (that would imply $\alpha<\beta$), and strict successors of $\beta$ cannot appear before $\beta$ in the order. At most the $L_X$ incomparable ones can occur. Thus the later rank is at most $h+i+j+1+L_X$ in this direction, or $h+i+j+1+L_Y$ in the other. Individually, these same bounds for each named high head imply $L_X,L_Y\ge h+\min(i,j)$ by (1).

Joint pooling and (1) now require
\[
 \boxed{\max(L_X,L_Y)\ \ge\ 2h+2\min(i,j)-1.}                  \tag{2}
\]
Indeed, if the maximum were at most $2h+2\min(i,j)-2$, the sum of the two first-high ranks would be at most $2h+2(i+j)+2+\max(L_X,L_Y)\le 2(\rho_R(u)+\rho_R(v))$ for every $R$. Joint pooling would then bound the sum of two high probabilities by twice the sum of two low probabilities, which is strictly less than $4/3$.

### Sufficient classes

* **Unbounded intertwined tails.** With the common chain prefix of length $h\ge2$, suppose each tail point is incomparable with at most $2h-2$ points of the opposite arm. Then there is a balanced pair. There is no restriction on either arm length: both incomparable high stretches in (2) are bounded by that local degree cap. In particular this includes arbitrary tails whose arm lengths are both at most $2h-2$.
* **Long crossed gates.** Index the arms starting at zero, assume $x_0<y_1$ and $y_0<x_\ell$ for some $2\le\ell\le\min(h+1,r-1)$, and suppose $r,t\le2h+1$. These hypotheses imply $x_0,y_0$ are low in any no-balance situation. First $\rho_R(x_0)\le h+2\le2h=2\rho_R(q)$; then $\rho_R(y_0)\le h+\ell+1\le2(h+1)\le2\rho_R(x_0)$. Thus $i,j\ge1$, so (2) needs one stretch at least $2h+1$, but both stretches are bounded by the corresponding suffix length at most $2h$. In particular this covers crossed, non-layered $4+4$ and $5+5$ tails even at $h=2$.

## A genuinely intertwined unbounded ladder

Take arm indices $0,\ldots,m-1$. In addition to the arm chains, impose $x_i<y_{i+1}$ and $y_i<x_{i+2}$ whenever the indicated labels exist, and take transitive closure. This is acyclic: every generating edge strictly increases the index. In fact all cross-arm comparabilities are exactly
\[
 x_i<y_j\iff j\ge i+1,\qquad y_j<x_i\iff i\ge j+2.
\]
The reverse implications follow directly from the respective generating cross edge and moving forward on its target chain. In the forward directions any path between the arms contains a first cross edge. A path starting on $X$ increases its index by at least one on that edge; a path starting on $Y$ increases it by at least two. Other edges never decrease the index. This rules out any further cross comparability from transitive closure.

The opposite-arm incomparable pairs are precisely $(x_i,y_i)$ and $(x_{i+1},y_i)$ when defined. Thus the whole incomparability graph of the tail is exactly the connected path
\[
 x_0-y_0-x_1-y_1-\cdots-x_{m-1}-y_{m-1}.
\]
It cannot split into a nontrivial ordinal sum, which would disconnect the incomparability graph. Its width is two (two arm chains and at least one incomparable pair). Appending this tail to a two-point chain prefix gives the local degree cap at $h=2$ for every $m\ge1$. Adjoining one isolated $a$ gives an actual ambient width-three poset realizing the exclusive branch, since $a,x_0,y_0$ are pairwise incomparable. The theorem also applies in any ambient poset satisfying the good-pair and probability hypotheses, not just that isolated realization.

For the minimal earlier missed crossed case $h=2$, $r=t=4$, take just $x_0<y_1$ and $y_0<x_2$ besides the arm orders. Single-target pooling alone cannot force either next head $x_1,y_1$ low from the two common points and the two low gates. After the prefix, place $x_0,y_0$ in either order, then $y_1,y_2,y_3,x_1,x_2,x_3$ or $x_1,x_2,x_3,y_1,y_2,y_3$. Each order satisfies the cross constraints, and the delayed head has rank 8. Distinct seed anchors sum to at most $3+4=7$; any proposed doubled gate can be chosen first, with rank 3. Joint pooling succeeds because the two head ranks always sum to at most 13, while twice the gate rank sum is at least 14.

The accompanying tiny deterministic script checks exact transitive closure of the ladder through $m=7$ and the rank statements for the crossed $4+4$ example. The proofs above cover every parameter and do not depend on enumeration. No new Lean compilation was performed; the cited Lean prerequisites are not an audit of the new joint lemma or structural theorems.
