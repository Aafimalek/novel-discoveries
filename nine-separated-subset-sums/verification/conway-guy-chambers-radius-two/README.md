# Exact local chamber obstruction at the nine-weight Conway–Guy witness

Let \(a=(77,117,137,148,154,157,159,160,161)\) be the
Conway–Guy witness. For each nonzero \(r\in\{-1,0,1\}^9\),
choose the unique orientation with \(r\cdot a>0\), once per
\(\{r,-r\}\). Thus there are 9,841 oriented signed relations.
An ordered unit-separated \(x\) is in a chamber when it satisfies
\(r\cdot x\ge1\) for each designated positive relation and
\(-r\cdot x\ge1\) for a designated flip. This is equivalent to
all 512 labeled subset sums being unit separated with the given
order. Distances here count *signed relation pairs*, not pairwise
subset comparisons (several literal comparisons can use the
same signed word), not Euclidean distance.

**Result.** No sorted chamber whose signs differ from \(a\) in
at most two oriented relations can improve its maximum below
161. In particular each of the six genuine single-wall neighbors
that reverse one of the first six Conway–Guy dual rows is excluded
by a small explicit positive dual, without an LP solve. This does
not rule out distant chambers.

## Starting representation and exact tight words

By the specialization at \(n=9\) of [Notik's Theorem 3.2](https://arxiv.org/abs/2611.17360),
there is the exact identity \(x_9=\sum_{j=1}^9 y_jR_j(x)\)
of linear forms, with the following rows and positive weights.
The table uses a dot for a zero coordinate.

| Row | Signed word | Weight |
|---|---|---:|
| \(R_1\) | ++++.-.-- | 1 |
| \(R_2\) | -++++-.-- | 1 |
| \(R_3\) | .-+++..-- | 2 |
| \(R_4\) | ..-+++.-- | 4 |
| \(R_5\) | ...-+++-- | 8 |
| \(R_6\) | ....-++.- | 15 |
| \(R_7\) | .....-++- | 25 |
| \(R_8\) | ......-+. | 48 |
| \(R_9\) | .......-+ | 57 |

Every listed row is CG-positive and evaluates to 1 at \(a\).
The weights sum to 161. The checker loops over the complete \(3^9\) ternary
words, including the zero word, then orients all nonzero
ones by their dot product with \(a\). There are exactly
12 CG-positive words of value 1. The three additional words
are \(E_j=R_7+R_9-R_j\) for \(j=1,2,3\), and are respectively
`----..+++`, `+----.+++`, `.+----+++`.
This classification is checked by full exact enumeration.
The proof of sign-distance obstruction does not depend on
having found every tight word; the classification is included
for reproducibility and to describe all tight neighbors.

## Genuine neighboring sign chambers

For *any* tight CG-positive word \(r\), put
\(s=\lVert r\rVert_2^2\) (its support size) and
\(a_*=a-r/s\). Then \(r\cdot a_*=0\).
For any other CG-positive word \(u\),
\(u\cdot a\) is a positive integer and \(u\cdot r\le s\).
Equality \(u\cdot a_*=0\) would force \(u\cdot a=1\) and
\(u\) to agree with \(r\) on every nonzero coordinate of \(r\).
Then \(u-r\) would be a nonzero ternary word supported in
the zero coordinates of \(r\) with \((u-r)\cdot a=0\),
impossible by distinct subset sums. Thus all the other
oriented words are strictly positive at \(a_*\).

More explicitly take \(\eta=1/(2s)\) and
\(a'=a-(1+\eta)r/s\). The flipped word has value
\(r\cdot a'=-\eta\). Every other tight word satisfies
\(u\cdot r\le s-1\), so \(u\cdot a'\ge1-(1+\eta)(s-1)/s>\eta\).
Every CG-positive word of value at least 2 at \(a\)
has \(u\cdot a'\ge1-\eta\ge\eta\).
Therefore \(2s\,a'\) has the single flipped orientation
and is unit separated. This is an explicit rational existence
witness for the adjacent sign chamber, not a low maximum witness.
For \(R_1,\ldots,R_7\) the sorted signs remain positive
(the changed word is not an adjacent singleton-order relation).
The checker also independently evaluates every oriented row and
sorts all 512 rational subset scores for each such witness.

## All single changes are blocked by written positive duals

If a unique sign flip is not one of the nine \(R_j\), their
original positive identity still gives \(x_9\ge161\), whether
or not the chosen non-tight word is actually a chamber wall.
Any exact equality with their unchanged constraints would
force \(R_j(x)=1\) for all \(j\); Notik's uniqueness in the
original nine-row system then gives \(x=a\), which cannot
realize any sign change.

If \(R_j\) alone flips for \(j=1,\ldots,7\), put \(k=8\)
for \(j\le5\) and \(k=9\) for \(j=6,7\). The word
\(U_j=R_j+R_k\) is itself ternary and has value 2 at \(a\),
so it keeps its positive sign. Replace the \(j,k\) terms
in the original identity by the exact combination
\[
 (y_k-y_j)(-R_j)+y_kU_j=y_jR_j+y_kR_k .
\]
Both coefficients are nonnegative. Therefore the cap lower
bound is \(161+y_k-2y_j\), respectively
\(207,207,205,201,193,188,168\). These need not be the exact
optima of the neighboring chambers; they suffice to reject a
cap of 161. Reversing \(R_8=x_8-x_7\) or \(R_9=x_9-x_8\)
is incompatible with the increasing order. For the extra
tight flips \(E_j\), the identity \(R_j=R_7+R_9-E_j\)
even strengthens the unchanged dual bound to \(161+2y_j\).

## Simultaneous two signs (static exact extension)

The only new cases to cover have exactly one or two basis
rows \(R_j\) flipped (only indices 1 through 7 are possible).

If two flipped rows are both in 1 through 5, their two
CG-positive \(U\)'s can both use the common \(R_8\)
budget: allocate nonnegative amounts \(z_i,z_j\) with
\(z_i+z_j=48\), \(z_i\ge y_i\), and \(z_j\ge y_j\).
The same substitution gives the bound
\(161+48-2(y_i+y_j)\ge185\).
If one is in 1 through 5 and the other in 6 or 7, their
ordinary substitutions use disjoint \(R_8,R_9\) budgets.
For the pair 6,7, instead use \(U'_6=R_6+R_8\)
for 6 and \(U_7=R_7+R_9\) for 7, again disjoint.
All words here are legitimate ternary words of CG value 2
and are not either flipped basis word.

If just \(R_j\) is flipped among the basis, the earlier
dual covers any second flip other than its companion \(U_j\).
For \(j\le5\), the twice-flipped case also has the ternary
word \(V_j=R_j+R_8+R_9=U_j+R_9\) (CG value 3) still
positive. Use the exact substitution
\[
y_jR_j+48R_8+57R_9
=(48-y_j)R_8+(57-y_j)(-U_j)+57V_j .
\]
This gives the lower bound \(161+57-3y_j>161\).
For \(j=6\), use the other companion \(U'_6\) instead,
yielding \(179\). For \(j=7\), \(U_7=x_7-x_6\) is
positive for every sorted candidate, so it cannot be the
second flip. These exhaust the two-sign cases.

## Exact replay

    sha256sum -c SHA256SUMS
    python3 check_neighbors.py
    python3 check_two_sign.py

Optionally, to materialize the six complete all-sign LP inputs
without running any LP solver:

    python3 check_neighbors.py --emit-lp ./six-models

The checker enforces every one of the 9,841 exact sign rows
in each rational witness, verifies all 512 subset scores
independently, and checks that every lower dual sums to the
objective with nonnegative coefficients on enforced signs.
The two-sign replay verifies a finite family of exact algebraic
dual substitutions; all other sign patterns in radius two are
covered by the reduction in the written proof. No numerical
optimization or Lean check is claimed.
