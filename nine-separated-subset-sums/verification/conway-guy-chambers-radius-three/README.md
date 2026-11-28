# The nine-weight Conway–Guy sign-radius-three obstruction

**Theorem.** Let \(x_1<\cdots<x_9\) be positive real weights with
pairwise unit-separated subset sums. If their signed-relation chamber
differs in at most three signs from the Conway–Guy witness
\(a=(77,117,137,148,154,157,159,160,161)\), then \(x_9\ge161\).
A sign here is one ternary word up to total reversal, not one literal
subset comparison or a Euclidean distance. No assertion is made about
distance four or more.

The exact radius-two package is included unmodified under prior-radius2/.
There, the 9,841 oriented words, all 12 tight relations, rational single-wall
crossings and objective certificates are independently checked. The present
proof starts with [Notik's identity](https://arxiv.org/abs/2611.17360)
\(x_9=\sum_{i=1}^9y_iR_i\), with
\[
(y_1,\ldots,y_9)=(1,1,2,4,8,15,25,48,57).
\]
Each \(R_i\) is a ternary word, CG-positive with value 1 at \(a\);
the explicit table is in prior-radius2/README.md. A positive dual
is an identity expressing \(x_9\) as a nonnegative combination of
the signed rows enforced in the chamber. Each such row is at least 1,
so its coefficient sum is a valid lower bound. We give a complete
support reduction and check every resulting nontrivial combination
by exact integer arithmetic. No optimizer is needed for the proof.

## Notation and substitution rules

\(R_8=x_8-x_7\) and \(R_9=x_9-x_8\) are always positive in a sorted
chamber. Thus only \(R_1,\ldots,R_7\) can be among the changed basis
signs. Write
\[
 U_j=R_j+R_8\ (j\le6),\qquad U'_6=R_6+R_9,\qquad
 U_7=R_7+R_9=x_7-x_6,\qquad V_j=U_j+R_9\ (j\le6).
\]
Every displayed \(U\) is a CG-positive ternary word of value 2;
every \(V\) is one of value 3, and \(V_6=x_6-x_5\) is always positive
in sorted order.

If a word \(p\) flips but \(p+k\) stays positive, a coefficient \(y\)
on \(p\) can be replaced using an available \(z\ge y\) from the
positive word \(k\):
\[
 yp+zk=(z-y)(-p)+z(p+k).
\]
This changes the lower bound by \(z-2y\). Several flipped basis
rows can share the same budget \(z_{\rm total}\) provided each
allocation is at least its own original weight.
When \(U_j\) flips but \(V_j\) stays positive, instead use
\[
 y_jR_j+y_jR_8+zR_9=(z-y_j)(-U_j)+zV_j,\qquad z\ge y_j.
\]
The gain is \(z-3y_j\), using only \(y_j\) of \(R_8\) and \(z\)
of \(R_9\). All unallocated positive terms are retained.
Only these simple substitutions and three integer identities below
are required.

## Complete partition by flipped basis rows

Any chamber of sign distance at most two is already covered.
For three flips, let \(m\) be the number of basis rows among them.

- **\(m=0\).** The original positive identity is unchanged.

- **\(m=1\), basis \(R_j\), \(j\le5\).** If \(U_j\) remains
  positive, the single-flip proof works. If \(U_j\) flips but
  \(V_j\) stays positive, use the second substitution with \(z=57\),
  as in radius two. The only remaining flip set is
  \(\{R_j,U_j,V_j\}\). Rewrite \(y_jR_j+y_jR_8+y_jR_9=y_jV_j\).
  Now apply the first substitution with flipped word \(p=V_j\) and
  \(k=R_6\) for \(j=1,2\), \(k=R_7\) for \(j=3,4\), and
  \(k=R_8\) for \(j=5\), using that word's entire remaining budget.
  The new word \(V_j+k\) is ternary and CG-positive of value 4.
  None of the three flips is that word or the reserve \(k\).
  The resulting bounds for \(j=1,\ldots,5\) are
  \(172,172,178,170,169\).
  For \(j=6\), if either \(U_6\) or \(U'_6\) stays positive,
  use that companion and its reserve. Otherwise both are flipped,
  and the second substitution with \(U_6,V_6\) gives 173; \(V_6\)
  cannot flip in a sorted chamber. For \(j=7\), use the original
  \(U_7\) certificate regardless of additional flips.

- **\(m=2\).** Start with the two-basis radius-two proof: rows
  \(R_1,\ldots,R_5\) use the \(R_8\) reserve, \(R_6,R_7\) use
  \(R_9\) if only one of them is flipped, and if both are flipped
  \(R_6\) uses \(R_8\) while \(R_7\) uses \(R_9\).
  The extra flip can affect this proof **only** if it is a
  designated companion; \(U_7\) cannot flip. Each such relevant
  case is covered as follows.

  - If a lower index \(j\le5\) has its \(U_j\) flipped and
    the other basis index \(i\) is at most 6, use the second
    substitution for \(j\) with \(z=57\); use the remaining
    \(48-y_j\) of \(R_8\) in the first substitution for \(i\)
    (so if \(i=6\), its companion is \(U_6\)).
    Its needed companion is different from \(U_j\), since
    adding the same \(R_8\) to two distinct \(R\)'s is injective.
  - If \(j\le5\) has \(U_j\) flipped and the other basis is 7,
    use \(z=32\) for \(j\), leaving 25 of \(R_9\) for the
    first substitution for \(R_7\). This gives
    \(161+7-3y_j\ge162\) for \(j=1,2,3\).
    For \(j=4,5\) use the identities in the next section.
  - If \(R_6\) and a lower basis row flip, and the extra change
    is \(U'_6\), use \(R_8\) for both substitutions (their required
    allocations total at most \(15+8<48\)); \(U_6\) remains
    positive. If \(R_6,R_7,U_6\) flip, use the last integer
    identity below.

  This is the whole list of harmful companion changes: each
  of the 21 pairs has two designated companions except that
  \(U_7\) is sorted-positive for the six pairs containing
  \(R_7\). Hence there are \(42-6=36\) exact obligations in
  this subfamily; an unrelated extra flip leaves the
  already verified radius-two dual untouched.

- **\(m=3\).** No companion flips. Use the same reserve rule:
  lower indices \(1\) through \(5\) share \(R_8\);
  \(R_6\) or \(R_7\) alone among the two uses \(R_9\);
  when both occur, \(R_6\) shares \(R_8\) with the one lower
  row and \(R_7\) uses \(R_9\). Three lower rows have weight
  sum at most 14, so their common reserve gives gain at least
  \(48-2\cdot14\). If both higher rows occur, the shared
  lower reserve has weights summing to at most \(15+8=23\),
  and contributes gain at least 2, plus 7 from \(R_7\).
  The remaining mixed case uses disjoint reserves and has
  even larger gain. The 35 three-basis sets are all verified,
  with minimum resulting proved lower bound 170.

## Three explicit exceptional integer duals

For the flip sets \(\{R_j,R_7,U_j\}\) with \(j=4,5,6\),
set \(\epsilon=0\) if \(j=4\) and 1 otherwise, and let
\(Q=R_j+R_7+R_9+\epsilon R_8\).
The table gives the new signed words, all coefficients on
the rows involved, and the overall lower bound.
Keep the original terms \((R_i,y_i)\) for
\(i\notin\{j,7,8,9\}\).

| \(j\) | CG-positive word \(Q\) | on \(Q\) | on \(-U_j\) | on \(-R_7\) | on \(R_8\) | cap lower |
|---|---|---:|---:|---:|---:|---:|
| 4 | ..-++.+-- | 57 | 53 | 32 | 101 | 270 |
| 5 | ...-+.+.- | 57 | 49 | 32 | 40 | 201 |
| 6 | ....-.++- | 57 | 42 | 32 | 33 | 180 |

The identities hold because the four replacements are
\[
57Q+(57-y_j)(-U_j)+32(-R_7)
 +(105-y_j-57\epsilon)R_8
 = y_jR_j+25R_7+48R_8+57R_9.
\]
Every \(Q\) is ternary and has positive CG value
\(3+\epsilon\), so it is not among the flips.
All multipliers are nonnegative, completing the proof.

## Exact replay

    sha256sum -c SHA256SUMS
    python3 check_radius3.py

The utility checks all actual used words have ternary coefficients,
checks their CG orientation by integer dot products, verifies the
model sign for each term, and checks exact objective identity and
nonnegative multipliers in each reduced case, including the three
exceptional certificates. It checks six one-basis chain cases,
36 two-basis companion cases and 35 three-basis cases. The written
case partition accounts for arbitrary other flips without an
exhaustive search through all sign patterns. The radius-two archive
can separately be replayed as documented there. No numerical
optimization or Lean checking is claimed.
