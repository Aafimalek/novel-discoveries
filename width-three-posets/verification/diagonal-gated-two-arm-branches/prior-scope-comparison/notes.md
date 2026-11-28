# Prior-scope comparison for an ambient diagonal ladder

Kevin Fathi's [November 3, 2026 working paper, v22](https://zenodo.org/records/23933091)
(indexed as [aiXiv:2611.00391](https://aixiv.online/abs/2611.00391))
reports balance for width-three posets whose maximum incomparability degree
is at most ten, and a stronger Gold certificate when there are no two
disjoint three-element antichains. The isolated-$a$ ladder fails the latter
exclusion comparison: every three-element antichain contains $a$. Its
degree exceeds ten for sufficiently long tails, so not every isolated
example belongs to the bounded-degree family.

The [newer November 19, 2026 working paper, v23](https://zenodo.org/records/24357683)
also reports a balanced pair at arbitrary degree in width-three posets
with three minimal elements or with three maximal elements. This update
matters: the ambient example below separates the two specified v22
hypotheses, but lies within the newer three-maxima theorem. It does not
establish novelty of the sufficient condition or an independent frontier.

## Exact ambient example

For $n\ge 5$ let $S$ be the ordinal sum of $b<q$ and the two
$n$-element rails $X=(x_0,\ldots,x_{n-1})$, $Y=(y_0,\ldots,y_{n-1})$.
Each rail is increasing. The cross generators are
$x_i<y_{i+2}$ and $y_i<x_{i+2}$ wherever defined. All cross comparisons
in their closure are exactly the corresponding index-gap-at-least-two
relations: the first cross edge of any directed path raises its index by
two, and a gate followed by the target rail realizes every larger gap.
Thus $x_i$ and $y_j$ are incomparable exactly when $|i-j|\le1$.

Adjoin $a,a'$ and impose exactly the additional strict generators
$a<a'$ and $b<a'$. Neither generator induces another comparison:
$a'$ is maximal, $a$ and $b$ are minimal, and no edge enters either $a$
or $b$. In particular $a,b$ are incomparable; $a$ has no predecessor;
$U(a)=\{a'\}$; $U(b)=(S\setminus\{b\})\cup\{a'\}$. The exclusive branch for
$(a,b)$ is exactly $S$. It has prefix length two and diagonal offsets
$(2,2)$, so the written structural rank-only theorem applies.

### Good-pair probability

Fix a linear extension of $S$, with $m=|S|=2n+2$. Its first point is $b$.
In the order with $a$ deleted, $a'$ can be inserted after any number
$k=1,\ldots,m$ of points from $S$. For each fixed $k$, exactly $k+1$
insertions of $a$ are allowed (the slots before $a'$), exactly one
of which puts $a$ before $b$. These are bijective enumerations, not a
product-measure assumption. Consequently,
$$
\Pr(a<b)=\frac{m}{\sum_{k=1}^m(k+1)}=\frac{2}{2n+5}<\frac12.
$$

### Exact scope checks

- The rails, with $b,q$ on one, and the chain $a<a'$ cover the poset by
  three chains. Two disjoint three-element antichains are
  $\{a,x_0,y_0\}$ and $\{a',x_1,y_1\}$. Thus width is exactly three.
- The point $a$ is incomparable to all $m=2n+2>10$ members of $S$.
  In fact its degree is the maximum $m$ (the degree of $a'$ is $m-1$,
  those of rail elements are at most five, and $q,b$ have degrees two
  and one). Thus the example also fails the degree-ratio and degree-range
  hypotheses stated in v23.
- On the four points $a,b,a',x_0$ the only strict comparisons are
  $a<a'$, $b<a'$, and $b<x_0$. This is the induced $N$. Its comparability
  graph and its incomparability graph are both connected paths. Every
  nontrivial parallel sum disconnects the former and every nontrivial
  ordinal sum disconnects the latter; either decomposition is hereditary
  under induced restriction. The ambient poset is therefore not
  series-parallel.
- Its two minima are $a,b$, and its three maxima are
  $a',x_{n-1},y_{n-1}$. Thus it is **covered by the three-maxima result
  reported in v23**. It also has an exact elementary symmetry exchanging
  $x_i$ and $y_i$ for every $i$, giving a balanced pair of probability
  $1/2$ in this specific example. The example separates hypotheses,
  not mathematical difficulty.

The two cited works are versioned author records. The comparison uses
their stated scopes, not an independent verification of their proofs.
No literature-wide novelty claim or claim about all width-three posets
is made.
