# Leaf-projection pressure in the four-isolate residual

**Written structural cut; not a Lean claim.** Apply the
[one-source reduction](../four-isolate-trace-enlargement/) and the
[leaf-deficient trace lemma](../four-isolate-leaf-deficient/). In the remaining
one-source case the source-containing family P has 15 members,
each containing all L leaves. The source-avoiding family B has
size b=2a+1, with leaf frequencies at most a−7, x-frequency a+1,
and each high isolate at most a. For every leaf l, the co-leaf
maximum U without p and l is a B-member, as is U without p.
The present argument does not require an additional assumption
on the nine full-leaf trace profiles.

## Projection and its mandatory deficiency

For each leaf l let

    D_l = { A in B : l not in A and A union {l} in B }.

Projection of the whole family G by deleting l preserves unions.
It also preserves the absence of seven-member strict chains:
choose preimages along a proposed chain and take their cumulative
unions, whose projections are the successive members of that
chain. The projected family has only nonempty members because
the original family has no singleton: if it contained {l}, unioning
with {l} would inject l-avoiding sets into l-containing sets other
than {l}, forcing a strict majority. The projected ground is smaller.

The only collisions are the two preimages in each toggle pair
indexed by D_l. In particular the p-containing sets do not
collide, because they all contain l, and no p-containing set
collides with a p-avoiding set. For each retained coordinate v,
the new total and frequency are respectively

    |G|−|D_l|,  f_G(v)−f_{D_l}(v).

Ground minimality forces a v with strict majority after projection,
or equivalently

    |D_l|−2 f_{D_l}(v) > |G|−2f_G(v).                 (1)

The right side is nonnegative. The witness cannot be p:
|D_l| ≤ f_B(l) ≤ a−7, so the projected B has at least a+8≥15
members, whereas p occurs exactly 15 times. For all other retained
ground points the co-leaf maximum belongs to D_l and contains
that point. Thus (1) implies |D_l|≥3 for every leaf l.

## Simultaneous cap on toggle supply

Let T be the isolate trace of A in B. Let r(A) be the largest
number of members in a strict B-chain ending at A. If t different
leaves can be individually adjoined to A while remaining in B,
union closure gives a strict extension chain of length t (t new
members) with constant isolate trace T. Any such member can then
be followed by 5−|T| members of P, from the full star with trace T
to the full ground (the trace {x} does not occur, so such a
maximal chain is always available). Therefore

    t ≤ |T| + 1 − r(A).

Summing these capacities across B gives

    3L ≤ sum_l |D_l| ≤ sum_{A in B} (|T(A)|+1−r(A))
         ≤ 4a+1.

The final inequality counts isolate incidences in B and uses
r(A)≥1; x contributes a+1 and the three highs at most 3a.

## Exceptions remove two possible witnesses in (1)

Call l exceptional at high isolate i if there is a three-chain
of B-members omitting l and with exact isolate trace {x,i}.
The preceding leaf-deficient argument showed that then all
members with trace {x,i} omit l, and the other two high isolates
j,k are twins on B_l, the whole family of B-members omitting l.

A member of D_l omitting j, equivalently omitting k, must have
isolate trace empty, {i}, or {x,i}. The empty trace supplies no
toggle pair: there is at most one B-member of empty trace.
Trace {x,i} likewise supplies no l-toggle because all of its
members omit l. The exact trace-{i} family has height at most
two by appending four p-containing members above any of its
members. It is union-closed, so the upper set in a strict pair
is its union maximum. For a given l, there is at most one
toggle pair with this maximum as its upper set.

Thus at most one D_l member omits the twin pair j,k, while the
co-leaf maximum is a D_l member containing both. This gives
2 f_{D_l}(j), 2 f_{D_l}(k) ≥ |D_l| and rules out either as the
witness in (1). A witness is still possible at x, at i, or at
another leaf; these are not excluded by the present count.

## Scope of the family-size bounds

The previous universal nine-profile bound is b≥4L+2c+1, where
the profile-specific constant c is read from the trace counts
and is at least 11. This gives b≥4L+23, at least 2L+25 for
L≥1 (with the same ground-minimal/no-strict-majority hypotheses
and nine-profile scope). The stronger b≥4L+51 is valid only
under the extra assumption that all three high types have
exceptional leaves. It cannot be stated as an unconditional
replacement for either lower bound.

The projection supply bounds do not give the required upper
bound on a. In particular neither supply from high-trace
members nor witnesses at x or at other leaves are controlled
enough to exclude a remaining full-leaf trace profile.
