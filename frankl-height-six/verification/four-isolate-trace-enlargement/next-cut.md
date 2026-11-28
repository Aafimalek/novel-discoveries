# Enlarging a source-avoiding fiber at four isolates

**Written necessary conditions with an exact finite replay.**
The residual family is *not* excluded. There is no new Lean claim.

Write p for the single source, L for the number of leaves, x for the
low isolate, and y,z,w for the three high isolates. Let B be the
source-avoiding members and b its size. The source-containing members
are the full star plus all 16 isolate traces except {x}. The previous
trace proof gives b odd, f_B(x)=(b+1)/2, each high isolate occurs at
most (b−1)/2 times, and every leaf at most (b−15)/2 times.
There are no B-members with trace {x}. The full B-top is U without p:
the source has no distinct forcing predecessor. More explicitly,
the checked avoidance characterization notMem_avoid_iff_forces says
that a ground point q is absent from avoid G r exactly when q forces
r. Thus avoid G p is U without p. For every leaf l, its only distinct
forcing predecessor is p, so avoid G l is U without p and l:
this is the checked lemma avoid_eq_coPair_of_edge in
FranklForcingFiber.lean, using weak ground minimality. Each maximum
belongs to G by avoid_mem_weak and avoids p, so they are members of
B. The B-top and the L co-leaf maxima are all distinct and all have
the full isolate trace.

## Co-pair forcing by filling a missing large set

The set C=U without p and x belongs to B. Otherwise add C to B.
The enlarged family is union-closed: every union of C with an old
member is C or the old full B-top. The new denominator is b+1.
The x-frequency does not change, and all other frequencies can rise
by at most one, so every point satisfies the weak half bound.

A chain containing C could be lifted to the original family by
replacing C with U without x and, if present above it, the full
B-top with U. The new chain is strict at every step since p is
absent below C, and both lifted sets are original members. Thus
the enlargement does not violate height six. Its ground still omits
p, contradicting ground minimality and proving C∈B.

## More general full-leaf trace enlargement

Let M be the set of isolate traces of members of B containing all
L leaves. It is union-closed, contains the full isolate set and
the high triple by the preceding argument, and avoids {x}.
Let V be the 15 trace sets other than {x}, and let W be any
upper set in V ordered by inclusion. Add to B all full-leaf sets
having traces in A=W without M. Closure holds: a union involving
an added set still has all leaves, its trace in V, and a trace
above the added one. Hence it is either old or added.

If there is a strict chain using an added set, leave the portion
strictly before its first added member unchanged. Lift that member
and all following members by adjoining p. Each such member has all
leaves and trace in V, so its lift is an original source-containing
member. Strictness is preserved (p was absent before the first lift,
and adjoining it to full-leaf sets preserves their strict trace
inclusions). Thus the enlarged family has height at most six.

Let a=|A|, and f_A be trace frequencies in the added sets. The
enlarged family would be a weak counterexample on smaller ground if

    2 f_A(x) + 1 ≤ a,
    2 f_A(v) ≤ a+1  for each v in {y,z,w}.

The inequalities use just the known B frequency margins. Each leaf
is present in all additions, but its original margin of 15 is
sufficient, since a≤15. The first inequality already implies a>0.
Therefore no candidate M may admit W satisfying these inequalities.

## Safe-trace refinement

Every trace T of B, even of a member with fewer than all leaves,
must be safe for M: T union R must belong to M for every R in M.
This follows by unioning the member with the full-leaf member
for R. There is at least one (in fact at least L+2) B-member
containing x and exactly one high isolate. Here is the counting
argument, independently of the enlargement cut.

Write A_j^+ and A_j^− for the number of B-members with x present
and absent respectively and exactly j high isolates. There are no
A_0^+ members. There is at most one A_0^− member, since a two-chain
of members with empty trace can be followed by a maximal five-member
chain in the source-containing traces (the full star with no
isolates, three successive high isolates, and then x). Counting all
high-isolate incidences by x-presence gives

    A_1^+ ≥ 2−A_0^−+A_3^++A_2^−+2A_3^−.

Indeed the x-present part contributes 2(b+1)/2−A_1^++A_3^+
incidences and the x-absent part contributes
(b−1)/2−A_0^−+A_2^−+2A_3^−; their total is at most 3(b−1)/2.
The B-top and every co-leaf maximum (omitting p and that leaf)
contribute to A_3^+, so A_3^+≥L+1 and A_1^+≥L+2.
Consequently M must admit at least one safe trace of the form
{x,y}, {x,z}, or {x,w}.

## Weighted obstruction for the safe traces

Fix any nonempty subset J of the three high isolates and assign
weight one to those in J and zero to the others. Put h=|J| and
score each trace by the number of its elements in J. Let u be
the minimum score among safe traces containing x, and v the
minimum among nonempty safe traces avoiding x. These minima exist as
the full isolate trace and the x-free high triple are both in M
and hence safe for M.

Write b=2a+1. The a+1 members of B containing x each have score
at least u, with L+1 known full-trace maxima each contributing
the extra h−u. The a members avoiding x include at most one with
empty trace; all remaining scores are at least v, and the forced
co-pair C has score h, contributing the extra h−v. Thus the
weighted sum is at least

    (u+v)a + u−v + (h−u)(L+1) + h−v.

It is at most ha, since each high isolate occurs at most a times.
If u+v≥h, this is impossible. In fact L≥1 implies that the
constant part is at least 3h−u−2v≥0, with equality only at
u=v=h. In that equality case the coefficient u+v=2h already
exceeds h, and a≥1 since the co-pair exists. Therefore each of
the seven nonempty choices J must satisfy u+v<h.

## Exact replay and limitation

Run python3 check_full_leaf_traces.py. It tests all 15-bit M masks,
all upper sets, and the seven nonempty weight supports. There are
2,214 union-closed M patterns with both required tops; 567 survive
enlargement; 283 also admit a requisite safe x-and-one-high trace.
The weighted test leaves 28 labeled patterns, or nine up to
permuting the three high isolates. The log lists canonical masks
for all nine. These are trace patterns, not actually realizable
family examples. The checks do not finish the four-isolate
single-source case.
