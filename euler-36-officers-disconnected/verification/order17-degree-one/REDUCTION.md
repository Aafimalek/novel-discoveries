# Mathematical coverage of the size-17 audit

Read [the README](README.md) and the manifest for exactly which formulas are checked.

## Common model and cuts

The base formula is the repository's pair/word encoding, with exact
cardinality 17 and with one degree-one label placed in group 0. A word
uses six pair projections; each used pair is supported by exactly one
word. Every candidate word has at least one used pair. A group degree
is the number of its used neighbors in any fixed different group.
The per-group sum of degrees above the minimum is therefore 17−6.
An all-degree-one selected word is isolated, which is inconsistent
with the prior disconnected minimum of 18.

The existing degree-order normalizations are applied only to free
labels. The anchored generators additionally reserve every label in
the specified words. The frequency constraints on anchor partners
are sorted across groups 1–3, which have the same role in the model;
in the normalized patterns, only partners of equal degree are freely
permuted to choose a diagram.

The rectangle cut is elementary: for an unused pair x,y, every pair
between the common unused-neighbor sets in the two other groups must
be used. With degrees ≤a,≤b these sets have size at least 6−a−b, and
a common used neighbor raises the lower bound by one. This is the
basis of all degree-threshold clauses for candidates in a rectangle.

For the high-partner cases, fix any two groups other than the leaf
group and take a maximum matching of t unused pairs among their five
nonanchor labels. At a matched unused pair, the two degrees sum to
at least 5, since all five nonanchor labels of the fourth group must
be blocked. In the unmatched rows and columns, all (5−t)×(5−t) pairs
are used, and for each matched edge at least one cross pair to any
unmatched row-column pair is used (avoid an augmenting path of
length three). Each paired unmatched degree sum is at least
2(5−t)+t. Thus the two anchored partner frequencies sum to at most
2·17−25. If a matching is perfect, each of the five nonanchor
fourth-group labels must occur ≥3 times, since a single occurrence
covers at most two matched cells. Its anchor frequency is then ≤2.
The solver clauses encode these necessary conditions by excluding
overlarge degree sums and by requiring some used edge in each
permutation matching when the omitted anchor's degree exceeds 2.
The same cuts apply to the smaller partner profiles.

## Reductions for minimum degree one

Any two degree-one labels in distinct groups must co-occur: an unused such
pair forces a used 4×4 rectangle on their other groups, and thus at least
four labels of degree ≥4 and two of degree ≥1 in a group, total ≥18.
Consequently any group outside A has all its nonanchor labels of frequency
at least 2. If at least two groups contain a leaf, each such group has
exactly one leaf, and all occur in the same word.

Let x be a leaf with word w. Suppose y is a nonanchor degree-two label in
another group, and one of its neighbors in a third group is the anchor
neighbor of x in that group. In the fourth group, the complement of
neighbors of x and y has size at least 3, all outside its anchor label;
in the shared-neighbor group it has size at least 4. Hence the three
candidate fourth-group labels have degree ≥4. Together with the other
two nonanchor degrees ≥2 and the anchor degree ≥1, this gives 17. Equality
requires exactly 3 degree-four and 2 degree-two nonanchor labels, and the
fourth-group anchor exactly 1. In particular, this configuration is
impossible when the fourth-group anchor has degree 2.

### Anchor pattern 122

The two extra words through the degree-two anchors in C and D are distinct
and cannot both use the same nonanchor values in groups A and B. Otherwise
their A–B pair repeats. By interchanging the two leaf groups, there are
only two normalized diagrams:
`1101,1210` (one member in A/B shared) and `1101,2210` (none shared).
Reserve all pinned labels. In either case the proof uses only the
standard pair/word constraints and the exact rectangle/degree cuts.

### Anchor pattern 222

All degree-one labels lie in A. Since every arrangement with a degree-one
anchor whose partner frequency ≥3 has been excluded, each of their words
has three partner labels of degree 2. Distinct leaves in A have disjoint
partner sets: if a partner were shared in one group, another group has
different partners (two shared partners would repeat a pair); the different
degree-two partner of one leaf would then share a used neighbor with the
other leaf in a third group, contradicting the rectangle cut above with
fourth-group anchor degree 2. The same cut forbids every used pair of
partners of different leaves in B/C/D. A nonleaf word also cannot contain
two partners of the same leaf, because their pair was already used by its
leaf word. Thus every nonleaf word contains at most one partner.

* Four or more leaves allow insertion: use one leaf and in B,C,D select
  partners from three distinct other leaves. All their pair projections
  are unused.
* With three leaves, pick an unpaired D label d. For each pair of B and C
  partners belonging to distinct leaves, choose the A leaf of the third
  index. Maximality forces d to be used with at least one of those two
  partners, so d's used edges cover the 6-cycle K3,3 minus its diagonal.
  This needs ≥3 edges for each of the three unpaired D labels, but only
  six B/C partner-extra occurrences are available in total.
* With two leaves, unpaired C/D has exactly 11 used pairs from its two
  B-partner extra words and nine all-unpaired words. For each B partner,
  using the other A leaf forces a full 3×3 rectangle on unpaired C/D,
  obtained by deleting the unique C and D neighbors of B outside partner
  labels. The two rectangles fit in 11 edges only if both excluded row
  and column are identical (otherwise their union has 12 or 14 edges),
  then their two B-partner extra words repeat this C–D pair.

Therefore the leaf in A is unique. Remove the original 0000 word and
the one extra word through each of B0/C0/D0. Each extra has exactly one
zero in B/C/D, so this leaves 13 core words on unpaired labels. Any
unpaired degree-two label in B/C/D cannot pair with the other groups'
partner zeros by the rectangle cut; thus it occurs only in core words.
Any two unpaired degree-two labels across B/C/D must pair in a core word:
otherwise they and the A leaf leave at least one fourth-group candidate
(degree bounds 1+2+2 < 6). Each unpaired group has frequency sum 15,
degrees ≥2, so it has at most 3 labels of degree 2. If one group has a
degree-two unpaired label and the other two do not, those other unpaired
groups have all degrees 3. Their pair projection has 14 used edges
(13 core plus the third partner extra), but a forced used 3×3 rectangle
would consume the selected rows' and columns' degrees, leaving at most
9+4=13 edges. This rules out a sole nonzero low count, hence also count 3
(since any degree-two label in another group would have to pair all three).

Further, if two groups have two degree-two unpaired labels each, their
four low–low pairs fill the 2×2 low–low block in core. The other nine core
words must fill their 3×3 high–high. The third partner's extra word then
repeats a high–high edge. Hence at most one group can have two low labels.
The nonincreasing low-count shapes reduce to 000, 110, 111, 210, 211.
The generating cases are implemented in `sources/pattern222.py`, and
`generate.py` runs them under the above unique-leaf reduction.

Within shape 000 each unpaired label in B/C/D has degree 3. If a regular
label were paired with both other partner zeros, it would leave only two
unpaired used neighbors in each of those groups, again forcing a 3×3
rectangle inconsistent with their 14 used pairs. So the two partner-extra
words through the other groups use distinct ordinary labels in each
coordinate. Only the three normalized diagrams
`1011 1102 1220`, `1011 1102 2220`, `1011 2102 3220` need be considered.

### Anchor pattern 112

The fourth-group degree-two anchor's other word normalizes to 1110.
If any nonzero member of 1110 has degree 2, use it against a leaf in a
different one of the first three groups. The equality rectangle above
forces the last of the leaf groups to have nonanchor degrees 4,4,4,2,2;
the two labels not in its candidate rectangle are exactly degree 2,
including its nonzero member of 1110. All three special labels are hence
degree 2, and each has as its two other low-group neighbors the special
labels and the unique other degree-two labels. In the core after deleting
0000 and 1110, their three remaining words must use low coordinates
(1,2,2),(2,1,2),(2,2,1) up to relabeling. This exhausts all low labels in
the first three groups. The other 12 core words would share only three
labels in each of those groups, impossible since 12 > 9. Therefore all
three specials have degree ≥3.

The core has 15 words and in each of its four groups all five labels have
core degree ≥2. In a leaf group, the special has core degree one smaller
than its full degree; all other unpaired labels (“ordinary”) have their
full degrees. Any ordinary core d2 label must be used with every core
d2 in each other leaf group (the fourth-group neighbor sets block ≤4
unpaired labels between them, and a third leaf has no pair with either).
If two leaf groups have ≥2 core d2s, each has an ordinary d2 and the two
counts are exactly 2. In their core pair matrix, if both specials are lows
then three low–low pairs are used in core (the fourth is used in 1110) and
one mixed pair each way; otherwise four low–low pairs use all their low
degrees. Either way the 15 core placements would require >9 high–high
pairs, impossible. At most one leaf group can have ≥2 core lows.

Let L be the number of degree-two unpaired fourth-group labels. If an
ordinary core d2 is used as one member of an unused pair with another leaf
in A/B/C, the two remaining groups (one leaf group and the fourth group)
have a forced used 3×3 rectangle in the 15-edge core projection. The
other-both block contributes at most four edges, so the cross edges
require ≥2 units of core-degree excess above 3 across these two groups,
bounded by their total number of core d2s (the core has 15 words and five
labels). This is true for each of the two other leaf groups.
* L=0: an ordinary d2 forces both other leaf groups to have ≥2 core
  d2s, already impossible.
* L=1: an ordinary d2 forces both other leaf groups to have ≥1 core d2.
* L≥2: any ordinary d2 must pair every fourth-group unpaired d2,
  otherwise another leaf and the two d2 labels leave an unused candidate.
  For L=2, a leaf group cannot have two ordinary d2 labels: their 2×2
  module would leave 11 high–high core pairs >9. If any ordinary d2 exists,
  the fourth group has no degree 5 (cannot pair that ordinary low).
  For L=3 an ordinary degree 2 cannot pair all three, so none exist.
* L>3 is impossible from degree sum and the frequency upper bound 5.

For a more symmetric SAT split pick a largest-degree unpaired fourth-group
label (degree h) and name it 5. Its h core words form a matching through
all three leaf groups; their special labels, if present, occur in distinct
words because special–special pairs were used in 1110. Permute the leaf
groups so that the k present specials are first and reorder the matching
words to put the special of present group j in word j. Relabel all other
values freely, reserving pinned labels for later sorting. Cases (L,h,k)
are (3,5,3),(2,5,3),(2,4,k),(1,4,k),(0,3,k), k=0..3 when h<5.
The generating cases are implemented in `sources/pattern112.py` and exposed
through `generate.py` as the `112-L-h-k` cases.
