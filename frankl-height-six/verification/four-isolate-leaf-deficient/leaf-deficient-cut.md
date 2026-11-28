# The leaf-deficient fibers at four isolates

**Written necessary conditions for the remaining 15-trace, one-source
case.** This does not exclude that case, and the lemmas are not yet
checked end to end in Lean.

Let p be the single source, U the ground, L the number of leaves,
and x the low isolate. Denote the three other isolates (the high
isolates) by i,j,k. The p-containing sets consist of the full
star plus any isolate trace other than {x}. The p-avoiding
family B has size b=2a+1. In B, x occurs a+1 times, each high
isolate at most a times, and each leaf at most a−7 times.
There is at most one B-member of empty isolate trace. The larger
top and co-leaf maxima are already known: the full top U without
p, each U without p and one leaf, and U without p and x all
belong to B. See the [preceding trace note](../four-isolate-trace-enlargement/next-cut.md) for their derivations.

## A three-chain forces a twin pair in a leaf-avoiding fiber

Fix a leaf l. For each high isolate i, let X_i consist of the
members of B with exact isolate trace {x,i}, and let X_i(l)
consist of members of X_i omitting l. For any member in X_i,
the three p-containing sets with successively enlarged trace

    {x,i} < {x,i,j} < {x,i,j,k}

give three strict extensions. Thus X_i has height at most three.
If X_i(l) contains a three-chain A1<A2<A3, then A3 is the true
union-maximum of X_i: otherwise append that maximum to the chain
before its three extensions. In particular every X_i member
omits l, not just members of the selected chain.

Suppose D in B also omits l and its trace contains exactly one of
j,k (there is no restriction on presence of x,i). The union of
A3 and D still omits l and has trace containing x,i and exactly
one of j,k. The following are seven strictly nested original
members:

    A1 < A2 < A3 < (A3 union D)
       < (U without p,l) < (U without p) < U.

The fourth inclusion is strict because the union omits one
high isolate. Thus no such D exists. Equivalently j and k are
twins on the whole subfamily B_l of B omitting l.

In particular if two different singleton-high x-containing
trace classes are nonempty on B_l, then neither can contain
a three-chain. Each nonempty class is then height at most two
on at most L−1 leaf coordinates (remove its fixed isolates),
so has at most L members. The same bound holds for a class
with a full-leaf member, even when no second class meets B_l:
that full-leaf member would itself strictly extend any three-chain
omitting l, contradicting the bound on the entire class.

If two distinct leaves are exceptional for distinct high
isolates, all three high isolates have identical occurrence
in the family omitting both leaves: use the two twin
relations. Thus that family has only traces empty, the
high triple, or the full isolate set. A trace {x} is forbidden.

## Lower bound on the unbounded source-avoiding family

Write M for the full-leaf trace family in B, m=|M|, and gamma_v
for the number of its members containing isolate v. For a leaf l,
the family B_l omitting l has size at least a+8, since l occurs
at most a−7 times in B. It is a smaller-ground nonempty
union-closed family of nonempty sets of height at most six,
so it must have a strict majority.

The following are upper bounds on its frequencies, subtracting
the already known members of B containing l:

- x: at most a+2−L−gamma_x. All full-leaf traces counted by
  gamma_x and the L−1 co-leaf tops not omitting l contain x.
- high v: at most a+1−L−gamma_v, by the same subtraction.
- another leaf: at most a−L−m−5. All m full-leaf traces and
  the L−2 co-leaf maxima omitting neither leaf count here.
  If there is no other leaf, this bound is unnecessary.

Compare twice these upper bounds with the lower bound a+8
on the denominator. The leaf constraint would only be tighter
if 2m+19 were smaller than both isolate thresholds, which
cannot happen since each gamma_v≤m. Thus, since some point
must exceed half in B_l,

    a ≥ 2L + min(2 gamma_x+5, min_high(2 gamma_v+7)).

For the nine canonical profiles from the preceding replay, the
additive constants are respectively 19, 17, 15, 17, 15, 15,
13, 13, 11. These are only lower bounds.

A second capacity estimate applies if there is a three-chain
exception for each of the three types. Let B_1 count all
members of B containing exactly one high isolate, and C_i
count the part whose unique high is i. Choose a leaf l_i which
has the exception at i. Every singleton-high trace other than
type i contains l_i, by the twin condition, so B_1−C_i≤a−7.
Adding the three inequalities gives 2B_1≤3(a−7). On the
other hand, if B_s counts members with s high isolates,
the degree sum over the three highs gives

    B_1+2B_2+3B_3 ≤ 3a,
    B_0+B_1+B_2+B_3 = 2a+1,

hence B_1≥a+2+B_3−2B_0. The top, L co-leaf tops, and
x-free high top yield B_3≥L+2, while B_0≤1. Thus in this
subcase B_1≥a+L+2 and a≥2L+25.

## Limitation

The three-chain rule controls shared leaf deficiencies and
forces an exact local twin structure otherwise. It does not
abolish the exceptional case: a singleton-high x-containing
class whose true top omits a leaf may still have height three,
if all members omitting that leaf have tied occurrence of the
other two highs. The linear inequalities here impose no upper
bound on a at scale L. No claim is made that all leaf-deficient
fibers have height two or that any of the nine profiles is
impossible.

The nine additive terms can be replayed with `python3 check_profile_constants.py`.
