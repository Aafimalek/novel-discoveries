# Rank constraints for nine separated subset sums below 150

Aafi Khan Malek, independent researcher, Ahmedabad, India · [aafimalek2032@gmail.com](mailto:aafimalek2032@gmail.com)

These are necessary conditions for the **next** real search, not an exclusion of the interval. The established bounds remain 149–161. The geometry and chamber implications below are written proofs; Lean checks the finite cut arithmetic and the basic paired-difference lemma separately. The companion Python script independently enumerates the external boundaries as sets of vertices and checks the listed arithmetic. No solver speedup is claimed.

See also the [central-gap addendum](central-gap-restrictions.md): all 197 central gaps are strictly below two, and two paired blocks of ranks have additional floor and coordinate-bit constraints.

## 1. Two forbidden edge bands

Let $1\le x_1<\cdots<x_9$ have pairwise unit-separated subset sums. Rank the sums from 1 to 512. A cube edge changing coordinate $j$ has rank length at most $\lfloor x_j\rfloor$; reversal by complement sends rank $r$ to $513-r$.

Write $m=\lfloor x_9\rfloor$ and suppose $149\le m\le 160$. If a cube edge has ranks $(k,k+L)$, normalize its lower rank to $l=\min(k,513-L-k)$ by complementing if needed. The edge is impossible under either of the following specifications as long as
$$
257-L\le l\le \left\lfloor(504-m)/2\right\rfloor:
$$
* $L=m$ and the edge changes coordinate 9 (the only possible coordinate at this length).
* $L=m-1$ and the edge changes coordinate 8.

**Proof.** Suppose such an edge changes coordinate $j$. Its real length is $t=x_j=L+\delta$ with $0\le\delta<1$. In the second case this follows from $x_8\le x_9-1<m$ and the assumed rank length. The $L+1$ sums in the edge interval $[b,b+t]$ have consecutive gaps of total excess $\delta$ over unit spacing. Consequently the floor of any positive difference in the interval equals its rank difference, and the fractional part is at most $\delta$.

Project these vertices by deleting coordinate $j$. Only the endpoints share a projection, so the projection has $L>128$ vertices. For each direction in the projected cube, one of the 128 pairs in its perfect matching lies entirely in the projection. For any coordinate $i\ne j$ of weight $x_i<t$, the positive difference of two in-interval lifts of such an edge is $x_i$ or $t-x_i$. In either case the fractional part of $x_i$ is at most $\delta$: if it were larger, the fractional part of $t-x_i$ would be $1+\delta-\{x_i\}>\delta$ as well. For every lift in such a direction, the positive difference thus has floor equal to the difference of the rounded subset sums in the same orientation.

There is one additional direction when $j=8$, namely coordinate 9. Two lifts of one of these projected edges can fit only with opposite bits in coordinate 8, and the lift with coordinate 9 present must omit 8. Their positive difference is $x_9-x_8\in[1,2)$, so its floor is 1, precisely $\lfloor x_9\rfloor-\lfloor x_8\rfloor$. The endpoints of the original interval also preserve rank difference under rounding.

The projection consists of the vertices whose sums lie in $[b-t,b+t]$. When all movable coordinates have weight at most $t$, connect any two vertices inside the slab by changing only their differing bits. While both additions and deletions are pending, pick an addition at sums at most $b$, otherwise a deletion. Each move stays in the slab. Finish monotonically toward the target. This proves connectivity directly for $j=9$, and within each fixed coordinate-9 fiber for $j=8$. In the latter case there is a matching edge across the two fibers by the $>128$ count, so the projection is connected. All paths lift to paths on in-interval vertices allowing the lifted moves above and the edge between the two lifts of the one duplicated projection. Therefore rank minus rounded subset sum is constant in the interval.

The reflected interval has the same property, and they overlap since $l\ge257-L$. The combined interval runs from rank $l$ to its complement $513-l$ and its real endpoints are symmetric about half the total real weight. Its half-width is at least $(513-2l)/2\ge(m+9)/2$. For a collision of rounded subset sums, first cancel the intersection. Add the same prefix of the unused coordinates to both subsets, choosing the prefix nearest half the unused rounded total. Consecutive prefix sums differ by at most $m$, so the two resulting rounded sums lie within $m/2$ of the rounded center. Changing from rounded to real scores shifts the deviation from the center by strictly less than $9/2$ (the deviation is a half-signed sum of nine fractional parts, all less than 1). Both lifted real sums are therefore strictly inside the connected interval, contradicting injectivity of rounded sums there. Global injectivity would contradict the [known integer optimum of 161](https://www.cecm.sfu.ca/~pborwein/PAPERS/P170.pdf), Table 5. ∎

## 2. Sixteen prescribed edges, all in coordinate 9

Suppose $149\le x_9<150$. The forbidden starts for length-149 edges are $[108,177]\cup[187,256]$. By [Harper's vertex-isoperimetric theorem](https://doi.org/10.1016/S0021-9800(66)80059-5), the first $k$ ranks must have at least 148 external neighbors for each of
```text
158 159 161 162 168 169 171 172
193 194 196 197 203 204 206 207
```
Indeed, the simplicial-order initial segment for such a $k$ consists of the 130 vertices of weight at most three and the first $k-130$ four-sets in lexicographic order. The boundary consists of the remaining four-sets and the five-sets whose lex-first four-subset was taken. A selected four-set $a<b<c<d$, with coordinates numbered 0–8, contributes exactly $8-d$ such five-sets. `RankCutTable.lean` checks the resulting counts and both required rank bands by definitional equality, with no axioms.

For these cuts, no edge from rank at most $k$ reaches $k+149$ or farther: reaching it would require a forbidden length-149 edge from rank $k$. Thus all ranks $k+1,\ldots,k+148$ must be external neighbors. The last must connect to rank $k$: rank $k-1$ would again require a forbidden length-149 edge, and earlier ranks are out of reach. The edge has length 148. No coordinate below 8 can give this length because $x_7\le x_9-2<148$; coordinate 8 is excluded by the second band above because the normalized starts lie in $[109,177]$. Hence **all sixteen prescribed edges change coordinate 9**, without assuming $x_8<148$. There are eight distinct pairs up to complement.

### Into a chamber search

Let $A$ be a subset of the eight smaller coordinates and write $s$ for their subset-sum function. The lower rank of the coordinate-9 edge over $A$ is
$$
1+\#\{B:s(B)<s(A)\}+\#\{B:s(B)<s(A)-x_9\}.
$$
Its rank length is $\#\{B:|s(B)-s(A)|<x_9\}$, including $A$: the base sets contribute one lift apiece to the half-open interval $(s(A),s(A)+x_9]$ exactly under this test. No other base set can sit on a threshold because the original subset sums are distinct. These comparisons depend only on signs already used in [Notik's chamber method](https://arxiv.org/abs/2611.17360). Partial sign assignments can bound both counts. A chamber can be rejected if for any of the eight representative ranks no $A$ can achieve that lower rank and length 148.

If the ordered base scores are $t_1<\cdots<t_{256}$, both sequences of lower and upper ranks, $j+\#\{i:t_i<t_j-x_9\}$ and $j+\#\{i:t_i<t_j+x_9\}$, increase by at least one at every step. Each consecutive required pair of lower ranks, such as 158 and 159, has consecutive upper ranks as well. The two edges must use consecutive base indices $j,j+1$; neither open interval $(t_j-x_9,t_{j+1}-x_9)$ or $(t_j+x_9,t_{j+1}+x_9)$ can contain a base score.

## 3. Two cheap search cuts below 161

If one replaces disjoint pairs of weights by their positive differences, the smaller configuration remains separated. To embed its sums in the original configuration, add the sum of the smaller member of every replaced pair; for each pair the embedded subset chooses exactly one member. Unused original weights may be dropped.

Using [Notik's exact real seven- and eight-weight results](https://arxiv.org/abs/2611.17360), any nine-weight configuration with $x_9<161$ satisfies
$$
x_7\ge84,\qquad x_6\ge44.
$$
First $x_8\ge84$ follows by retaining eight weights. Thus $x_9-x_8<77$. Replace this pair with its difference and keep the first seven weights. This separated eight-weight configuration has a weight at least 84, so $x_7\ge84$. Finally at least one adjacent gap among $x_7,x_8,x_9$ is below $77/2<44$. Keep the first six and the difference of this adjacent pair (dropping the third large weight). The separated seven-weight configuration needs a weight at least 44, so $x_6\ge44$.

### Exact coarse root benchmark

The prototype `root_filter.py` bounds each signed comparison over the closed interval $149\le x_9\le150$ and the singleton spacing constraints. It does not assign unknown chamber signs or solve a floating-point LP. Writing $x_i=i+\sum_{j\le i}g_j$ and adding slack $g_{10}=150-x_9$, the $g_j$ are nonnegative, sum to 141, and have first-nine total at least 140. With the additional cuts the first-six and first-seven totals are at least 38 and 77. Equivalently, the gaps are the sum of budget vectors of sizes 38, 39, 63 and 1 allocated respectively among the first 6, 7, 9 and 10 slots: select each component successively from the remaining gap mass in its allowed slots. Therefore each extremal signed comparison is obtained by putting each budget in an allowed slot of minimal or maximal coefficient. Comparing those integer bounds with $-1$ and $+1$ yields the possible signs under separation.

For each prescribed rank the table counts possible base masks of the 256 after independently bounding lower rank and edge length:

| Lower rank | 158 | 159 | 161 | 162 | 168 | 169 | 171 | 172 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Singleton spacing only | 129 | 129 | 129 | 129 | 131 | 129 | 130 | 130 |
| Also using $x_6\ge44$ and $x_7\ge84$ | 124 | 124 | 124 | 123 | 123 | 122 | 122 | 122 |

This is a candidate-count benchmark, not a benchmark of search-tree size or wall time. Every rank still has candidate masks.

## Reproduction and scope

```sh
python3 rank_cuts.py
python3 root_filter.py
lean RankCutTable.lean  # Lean 4.36.0, no Mathlib required
lake env lean PairDifference.lean  # From a project with Mathlib
```

`RankCutTable.lean` checks finite arithmetic. `PairDifference.lean` proves the single-pair separation lemma by an injective, constant-translation map on subsets. It uses Lean’s standard axioms only; Mathlib was pinned at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Neither file formalizes Harper's theorem, the connection from the shadow arithmetic to general cube boundaries, either real rounding band, Notik's theorem, or the real optimization. ChatGPT assisted with the proof development and verification; Codex was not used.
