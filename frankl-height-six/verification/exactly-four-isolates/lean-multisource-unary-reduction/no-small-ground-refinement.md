# Removing the external small-ground theorem from the four-isolate multi-source case

**Written refinement, not yet Lean-checked.** The goal is the same
exactly-four-isolates multiple-source exclusion as in the existing
note. The following changes remove its external 12-point input.
They also simplify the all-pair branch. The earlier deficit
reduction and the large deficit-one/two combinatorics are unchanged.

## No pairs and the four-point capacity

A weak counterexample has no member of size two. If {x,y} were a
member, adjoining it would inject sets containing neither x nor y
into sets containing both. The pair itself is not reached because
the original family contains no empty member. But the weak frequency
bounds give that the both-containing count is at most the neither
count, a contradiction. Together with the existing singleton and
empty exclusions, every family member has cardinality at least three.
Consequently the number of original members that fit inside any
fixed four-point support is at most five (four triples and the
full support).

If one source is multileaf and another source exists, the checked
cross_pair_top_subset_isolated_of_multileaf says their anchored
leaf-pair avoidance family is supported only on the isolated
points. At exactly four isolates this gives at most five members.
The checked terminal_pair_avoidance_card gives at least n−1
members, where ground size n≥4+2k≥8 because each source has a
distinct leaf and k≥2. Contradiction. Therefore every star is
unary, without a general small-ground theorem.

## All blocks are pairs, including k=2,3,4

Use Q=binom(k,2), H(m)=1+m+binom(m,2), and m=k+2. A fixed
pair fiber has baseline lower Q+k+6 and at most H(m)
members. If k=2, its support is just the four isolates;
the preceding capacity five contradicts baseline Q+k+6=9.

Suppose k≥3. The rank-two atom lemma on the compressed
complemented fiber, with a atoms and at most m support
coordinates, gives at most 1+m+binom(a,2) members. Thus
a≥m−1, because for a≤m−2=k this is at most Q+k+3 below
baseline. From each pair block through a source r, the actual
sets omitting exactly those two stars supply one of three
lists of exact isolate omissions:

- Type A: at least three singleton isolate omissions.
- Type B: two singleton isolate omissions and the pair of
  the two other isolates (one two-coordinate atom).
- Type C: a singleton {x} and all pairs {x,y} with y≠x.
  This occurs when the true support misses one coordinate,
  necessarily an isolate (the omitted block is exactly the
  anchor pair). Then the true support has m−1 singleton atoms,
  so dropping no support coordinate or one of its other
  isolates gives the indicated actual omissions.

For full support, the classification follows from fitting at
least m−1 disjoint nonempty atoms into m slots: either all
but at most one coordinate are singleton atoms, or exactly
two coordinates form a double atom. Missing support cannot
lose two coordinates because a≥m−1.

Any two such lists contain two omissions with a nonempty
intersection. For A/A or A/B their singleton lists intersect.
For B/B either a common singleton exists or the double atom
of one contains a singleton of the other. For A/C or B/C,
intersect any singleton of A or B with a suitable member of C.
For C/C the anchors of the lists are either equal (common
singleton) or different (their pair is in both lists).
Because k≥3, use two incident pair blocks through r. Unioning
their original family members gives one mixed omission
S_r union J with nonempty J (S_r is the complete unary star).
For any fixed fiber the k−2 other sources give at least k−2
extra pair-containing witnesses, as in the existing mixed
omission count.

If any fiber had a≤m−1, its cardinality would be at most
1+m+binom(m−1,2)=Q+2k+3, leaving at most k−3 slack
over its baseline Q+k+6. The k−2 extra witnesses exceed this.
Consequently every pair fiber has its full m singleton atoms,
full support, and all relative singleton omissions. It follows
that every source r gives four mixed omissions, one for each
isolate (take any two incident blocks). If k≥4, then

    4(k−2) > H(k+2) − (Q+k+6) = 2k−2,

a contradiction. This includes k=4 (8>6).

If k=3, then 4(k−2)=2k−2=4. Hence all three pair fibers
must be saturated at H(5)=16. With m singleton atoms,
each nonatom uses at least one unordered coordinate pair
and distinct nonatoms share no pair (their intersection
is empty or a singleton). Saturation forces every pair
to occur and every nonatom to consist of exactly two
coordinates. Thus every pair fiber has all relative
two-isolate omissions. Unioning the corresponding original
sets from two blocks through r gives another mixed omission
S_r union {x,y} distinct from the four singleton ones.
This exceeds slack four even at k=3.

## Deficit one and two at small k

Maximum deficit one means disjoint triples. With k=2 it
cannot occur (the only pair-design block is a pair).
With k=3, its sole triple leaves four isolate coordinates,
so the upper bound is H(4)=11, whereas the lower is
N+k+8=1+3+8=12.

With k=4 and deficit one, there is one triple T and one
regular source q. An ordinary pair anchor (p,q) with p in T
has at most five coordinates after the two other triple
vertices are grouped, lower Q+k+5=15, and H(5)=16. Thus
it has full support and all singleton atoms by the rank-two
bound (if a≤4, capacity only 12). An anchor pair inside T
omits all of T and leaves five coordinates; its lower
Q+k+6=16 saturates the same upper bound, also giving
full support and all singleton atoms. For each r in T,
use the anchor block {r,q} and an anchor block T: they
intersect only at r. Singleton-isolate omissions from
both yield the four mixed omissions S_r union {x}.
For the ordinary pair anchor (p,q) the exterior triple
source r alone supplies four extra witnesses, greater
than the slack 16−15=1. Thus k=4 is also impossible.
The existing deficit-one argument applies for k≥5.

Maximum deficit two cannot occur at k=2 or k=3, since
g≥1 and d=k−1−g. At k=4 it must be a single four-block:
two triples through a point use five distinct vertices
(by pair uniqueness), and no other nonpair size is
possible. A pair within the four-block has four isolate
coordinates, upper H(4)=11, and lower
Q−5+k+10=15. This excludes k=4. The existing general
quad/dual-graph argument for deficit two applies for k≥5.
The earlier proof of maximum deficit at most two involves
only d≥3, hence k≥d+2≥5, and is unaffected.

Thus the written multiple-source proof no longer needs any
external small-ground theorem. The zero-source case at
exactly four points is also elementary: every member has size
at least three, so summing point frequencies gives at least
3|G| incidences; the weak threshold on four points allows
at most 2|G|. This note makes no new kernel claim.

## Exact prior dependencies and the extra count

The following inputs are used from earlier proofs, not reproved in
this refinement.

- **Forcing structure.** Minimal weak families are separated, have no
  two successive proper forcing arrows, and each point has at most
  one proper forcing predecessor. In the Lean foundation see
  weakMinimalGround_separated, noThreeForcingChain_of_separated,
  weakMinimalGround_unique_proper_predecessor and partition_card,
  together with sources_card_le_leaves. The present small-support
  step uses cross_pair_top_subset_isolated_of_multileaf and
  terminal_pair_avoidance_card, as named above.
- **The original lower bound.** Omitted-star blocks satisfy
  starBlocks_pairDesign. The away-count identity is
  W+g_p+g_q=N+1 (away_and_two_designDegrees). The checked
  leaf_pair_count_with_blocks gives |F_pq|≥n+k+W−1. Combining
  n≥2k+4 with g_v=k−1−d_v yields
  |F_pq|≥N+k+6+d_p+d_q. At k=2 in the all-pair case,
  W=0, N=Q=1 and n≥8, so this is the explicit bound nine;
  it is not deduced from a nonempty outside source set.
- **Isolation of mixed witness counts.** A mixed omission
  U without (S_r union J), for a nonempty isolate set J and
  a unary star r outside the anchors, contains both anchor
  leaves. Its complement has at least three original points,
  so it is neither U nor any single-point avoidance maximum:
  the complement of avoid(v) is v plus its at most one
  proper predecessor, by notMem_avoid_iff_forces. It misses
  a leaf of S_r, so it is not a sourceWitnessTop (those
  contain every leaf). It misses exactly one full star, so
  it is not a pair maximum (which misses at least the two
  anchor stars of that maximum). Mixed omissions for
  different r or J are distinct by taking complements and
  separating the star points from isolates. Hence these
  witnesses really add to the old lower bound. In Lean
  this is the existing terminal_pair_avoidance_extra_noncanonical
  applied to the union of the two old witness collections
  and the new disjoint one; the general three-way wrapper
  still needs to be written.
- **Compression and extremal bound.** Existing cross-pair
  compression preserves union, cardinality and strict
  inclusion in the needed directions; stars outside the
  omitted block are whole or absent. The sharp support
  bound is pair_fiber_card_le_sauer_block_signatures. The
  refined atom inequality 1+m+binom(a,2) is the separate
  written exact-three lemma (atom geometry is now staged
  as a new Lean draft; the count is not yet formalized).
- **Deficit reduction and the remaining large branches.**
  Section 1 of the preceding exactly-four note gives d≤2:
  the Cauchy degree bound N≥k g²/(k−1+g) yields d≤7,
  lost-block charge 3(Q−N)≤2kd gives the refined slack,
  and at d=3,4,5 a single extra signature merge exceeds
  slack, forcing all nonpairs through the minimum-degree
  anchor and the contradictory convex loss bound.
  The d=1, k≥5 proof is the disjoint-triples
  count in Section 4 of that note. The d=2, k≥5 proof
  is its four-block and triple-dual-graph Section 5.
  Those components continue to be written rather than
  wholesale Lean dependencies of the present refinement.
