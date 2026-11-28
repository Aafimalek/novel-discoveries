# Central gap restrictions below 150

These are necessary conditions, not an exclusion of the interval. Suppose nine positive weights have 512 pairwise unit-separated subset sums and that their largest weight is $M=149+\delta$ with $0\le\delta<1$. Write $s_r$ for the subset sum of rank $r$, $g_r=s_{r+1}-s_r$, and $e_r=g_r-1$. Use the [forced rank pairs](README.md), including $(158,306)$ and $(172,320)$, each differing by the largest coordinate.

## Every central gap is strictly below two

Consider the rank interval $I=[158,306]$. Its 148 consecutive gaps have total excess $1+\delta$. Suppose one of them, $g_q$, is at least two. Subtract one unit of excess at $q$. The remaining excesses are nonnegative and sum to $\delta$. Thus, with the augmented rank $R(r)=r+\mathbf 1_{r>q}$, for any $r<t$ in $I$ we have
$$
R(t)-R(r)\le s_t-s_r\le R(t)-R(r)+\delta.
$$
In particular the positive gap has floor equal to its augmented rank difference and fractional part at most $\delta$.

Delete the largest coordinate from the 149 subsets in $I$. Only the two endpoints have the same projection, because two distinct lifts of any projection differ by the full interval length $M$. The projection thus contains 148 vertices, more than half of the eight-cube. For every smaller coordinate $i$, the matching along that direction contains a pair in the projection. Any two lifts of such a pair inside $I$ differ in score by $x_i$ or $M-x_i$ in absolute value; $M+x_i$ cannot fit. This implies $\{x_i\}\le\delta$: if $\{x_i\}>\delta$, then $\{M-x_i\}=1+\delta-\{x_i\}>\delta$ as well. Thus, writing $a_i=\lfloor x_i\rfloor$, the floor of every such positive lift difference is the corresponding oriented difference of rounded sums. The two original endpoints also satisfy the equality because their augmented rank difference is 149.

As in the main [slab proof](README.md), the projection is the connected band of base scores between $s_{158}-M$ and $s_{158}+M$. To reach a target in the band, while both additions and deletions are pending, add at or below the midpoint and subtract above it; then finish monotonically. Projected paths lift by allowing the in-interval moves and, if needed, the move between the two lifts of the original endpoints. Therefore augmented rank minus rounded sum is constant on $I$. The rounded sums increase strictly with real rank there.

Complement sends $I$ to $I'=[207,355]$ and preserves the strict increase. The overlapping intervals cover $[158,355]$, so the rounded sums strictly increase on the full interval, even if the augmented ranks have different origins. Its endpoints have real half-width at least $197/2=98.5$ about the true center. For any collision of rounded subsets anywhere, cancel the intersection and add the same prefix of unused weights to both, chosen to put the common rounded score within $149/2$ of the rounded center. The two real scores are then strictly less than $149/2+9/2=79$ from the true center, since the deviation changes by a half-signed sum of nine fractional parts. Both scores must occur in $[158,355]$, impossible. Global rounded injectivity would give nine distinct-sum integers with maximum 149, contradicting the [integer bound of 161](https://www.cecm.sfu.ca/~pborwein/PAPERS/P170.pdf) (Table 5).

This excludes any gap at least two in $I$, and by reflection in $I'$. Thus $1\le g_r<2$ for all $158\le r\le354$. At the central cut, ranks 256 and 257 are complements. They give a full sign vector $\varepsilon\in\{-1,1\}^9$ with $1\le|\varepsilon\cdot x|<2$. Every other full sign vector, except its negative, has absolute value at least $|\varepsilon\cdot x|+2$: its complementary pair is at least one rank farther out on each side. This is a disjunctive chamber constraint, not a specific choice of signs.

Let $g=g_{256}$ and orient the central sign pattern so that $\varepsilon\cdot x=g>0$. For a nonempty proper support $S$, set $D_S=\sum_{i\in S}\varepsilon_i x_i$. Flipping the signs on $S$ gives another full-support choice, with absolute sum $|g-2D_S|\ge g+2$. Equivalently,
$$
D_S\le-1\qquad\text{or}\qquad D_S\ge g+1.
$$
For example, if $\varepsilon_1=+1$ this gives $x_1\ge g+1$. For any adjacent signs $\varepsilon_i=-1,\varepsilon_{i+1}=+1$, it gives $x_{i+1}-x_i\ge g+1$. The exact coarse test in [middle_partition_root.py](middle_partition_root.py) checks these simple cuts together with the existing two root inequalities and $149\le x_9\le150$. It leaves all 220 patterns that met the raw root extrema: the simple cuts do not reduce the number of central orientations at this coarse stage. This is not a benchmark of a full chamber search.

More generally, the $p$-th smallest absolute full-support sum is $s_{256+p}-s_{257-p}$. For $1\le p\le64$ both ranks are in the forced interval $[172,320]$, so the value is between $2p-1$ and $2p+\delta$. The first value has the stricter upper bound above.

## Two blocks have total excess at most half the interval excess

The two prescribed edges from ranks 158 and 172 give
$$
s_{172}-s_{158}=s_{320}-s_{306}.
$$
Reflecting the second difference about the total-score center gives $s_{207}-s_{193}$. Hence the gaps with indices 158–171 and 193–206 have equal total excess. They are disjoint within $I$, whose total excess is $1+\delta$. Each block has excess at most $(1+\delta)/2<1$. Thus for any two ranks in either $[158,172]$ or $[193,207]$, and likewise in their complemented blocks $[341,355]$ and $[306,320]$, the floor of their positive real difference equals the rank difference.

For every integer $158\le r\le172$, the subset at rank $r$ and the subset at rank $r+148$ have opposite largest-coordinate bits. In fact, $(r,r+148)$ is an edge in that direction exactly when the subset at rank $r$ omits the largest coordinate. To see this, if the subset at $r$ omits the coordinate, add its weight. The result is in the upper block, and the integer part of its displacement from $s_{306}$ is $r-158$, so its rank must be $r+148$. Conversely, if the subset at $r+148$ contains it, subtract its weight; the lower block identifies rank $r$ by the same calculation. Complement supplies the reflected rule.

## Sharpening the two forbidden bands

The upper endpoint for the forbidden normalized starts in the [main proof](README.md#1-two-forbidden-edge-bands) can be increased from $\lfloor(504-m)/2\rfloor$ to $\lfloor(506-m)/2\rfloor$ for both coordinates. The lower endpoints stay unchanged. For $m=149$ the forbidden length-149 band becomes $[108,178]\cup[186,256]$.

Here is the improved centering step, in the notation of that proof, for $149\le m\le160$. For a rounded collision, let $A,B$ be the disjoint nonempty parts after cancellation and $C$ the unused coordinates. Rather than centering the rounded common sum, choose the prefix of $C$ closest in **real** weight to half the real total of $C$. The midpoint error of the translated real pair is at most half the largest unused real weight. The pair's half-separation is half the absolute difference of the fractional weights on the two colliding sides.

If $C$ is empty, the latter error is less than $9/2$ and the real midpoint is exactly central. If $C$ is nonempty, each colliding side has at most six coordinates. Indeed a side of size seven would leave a single coordinate on the other side and one unused, so the total rounded weight would be at most $3m$. The total real weight would then be less than $3m+9\le489$, below the required total of at least 511.

For a saturated coordinate-9 interval, all fractional parts are at most its excess $\delta$. This bounds the half-separation by $3\delta$, and the midpoint error by $(m+\delta)/2$. The total radius is less than $(m+7)/2$. For the coordinate-8 interval of rank length $m-1$ and excess $\delta$, the smaller fractional parts are again at most $\delta$. The projected coordinate-9 swap has difference $1+\{x_9\}-\delta$, so $\{x_9\}\le2\delta$. If 9 is unused the half-separation is at most $3\delta$ and the midpoint error is less than $(m+1)/2$. If 9 is used the half-separation is at most $7\delta/2$ and the midpoint error is at most $(m-1+\delta)/2$. Thus the radius is less than $(m+7)/2$ in all cases. The complement interval has half-width at least $(513-2l)/2$ for normalized start $l$. This is at least $(m+7)/2$ when $l\le\lfloor(506-m)/2\rfloor$, so the collision contradicts the same rounded injectivity argument.

The same calculation gives parameter-sensitive sufficient upper bounds. For the length-$m$ edge along 9, write $\theta=\{x_9\}$: it is forbidden when $513-2l\ge m+7\theta$ and the original overlap condition holds. For the length-$(m-1)$ edge along 8, write $\delta=\{x_8\}$ and $\theta=\{x_9\}$. The swap gives $\delta\le\theta\le2\delta$. The radius bound is $(m+\theta+6\delta)/2$ when 9 is unused; when 9 is used the bound $(m-1+8\delta)/2$ is smaller. Equality at the boundary suffices because the rank interval is closed. For $m=149$, in either case, normalized starts 179, 180, or 181 are forbidden if respectively $\theta\le6/7$, $\theta\le4/7$, or $\theta\le2/7$, provided the usual overlap. If $x_9=m$ is itself an integer, a rank-length-$m$ edge along 9 is impossible anywhere: the vanishing excess and the projected matching force every smaller weight to be integral without a centering argument.

## Independent distance-to-integers cut

If $x_9<160.5$, round each weight to a nearest integer. The resulting positive integers all have maximum at most 160, so some distinct subsets have equal rounded sum. Cancel their common elements and apply unit separation to the two disjoint real subsets. Their difference in rounding errors has magnitude at least one. Consequently
$$
\sum_{i=1}^9\operatorname{dist}(x_i,\mathbb Z)\ge1.
$$
Likewise the distance in $\ell_1$ to any fixed positive integer vector of maximum below 161 is at least one.

## Four affine packing cuts

Let $S=\sum_i x_i$. Pair the largest $2d$ weights consecutively in their sorted order, and replace each pair by its positive difference. The new $9-d$ weights still have unit-separated subset sums: translate by the sum of the smaller member of every pair, turning each new subset into a distinct original subset. Their total is at least $2^{9-d}-1$, the number of unit gaps in the entire sorted subset-sum list. Thus, for $d=1,2,3,4$,
$$
S-2(x_8+x_6+\cdots+x_{10-2d})\ \ge\ 2^{9-d}-1.
$$
These four constraints require no smaller-dimensional optimum theorem. Among disjoint choices of $d$ pairs, the choice stated maximizes the sum of the lower members: the largest lower member is at most $x_8$, the next at most $x_6$, and so on.

An LP benchmark closes both $x_9<150$ and the central gap bound $g<2$ at their upper endpoints, safely relaxing the search. It adds these four cuts to the ordered singleton gaps, $x_6\ge44$, $x_7\ge84$, $S\ge511$, and the central orientation cuts above. Of 512 full-support central orientations, **292** are excluded without the four packing inequalities and **294** with them. The **218** survivors are *not excluded by this root test*, not viable separated configurations. The two extra exact rejections are recorded alongside the full tables. The floating-point solver only finds candidate certificates; each rejection is verified exactly with rational Farkas multipliers $y\ge0$, $A^\mathsf{T}y=0$, $b^\mathsf{T}y<0$ for that branch's inequalities $Ax\le b$.

Replay the certificates with standard Python (no LP solver required):
~~~sh
python3 central_root_lp.py central-root-farkas.json --verify-only
~~~
To regenerate them with SciPy/HiGHS, omit the flag.

The proofs are written mathematics. The accompanying Lean file checks only the finite index identities for the interval argument, not the real inequalities, geometric steps, or the remaining gap.
