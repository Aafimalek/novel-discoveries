# Sign-flip and adjacent-swap orbits at two rank holes

Suppose a consecutive run of prescribed rank-148 edges gives the
base-eight slots q_min through 64, as in the [rank-run
construction](../hall-rank-runs/). Let a and b be the common threshold
counts, so a+b=148 and 64≤a≤74. Set W=66−q_min. The two gaps in the
ordered absolute signed sums, at ranks a and b, each have width at
least 2W. Indeed the earlier +2 endpoint bounds give jumps of size
at least alpha[q_min]−alpha[64]+4, and the signed-sum spacing gives
alpha[q_min]−alpha[64]≥2(64−q_min).

Flipping the sign of a coordinate of weight less than W changes
the absolute signed sum by at most twice that weight. Swapping two
adjacent signs whose corresponding weights differ by less than W
also changes the absolute signed sum by at most twice their weight
difference. Neither operation crosses either gap. These moves commute
with complementing all signs, so they act on the 128 complementary
pairs. The subsets below the two gaps are nested unions of the
resulting orbits. Hence each orbit must fit entirely in one of the
three regions of sizes

    a, 148−2a, a−20.

The exact replay finds the connected components of the sign-action
graph (the orbits), then packs their sizes into the three regions
using a two-region finite dynamic program. The remaining size is
automatic since there are 128 pairs.

Consequences:

1. At most two of the eight weights can be less than W. For any s≤7
   certified small coordinates, fix the sign of some other coordinate
   and flip the s coordinates independently. Orbits have size 2^s
   so 2^s must divide both a and 148. In particular three small
   weights would imply 8 divides 148, which is false.
2. Some adjacent weight difference among the first eight is at least W.
   Otherwise all seven adjacent swaps operate, generate every
   permutation, and give orbit sizes 1, 8, 28, 35, 56. None can be
   packed into the required region sizes.
3. If every gap but the first or the seventh is below W, the only
   possible count is a=70. The replay also lists the excluded counts for
   each potential interior large gap.

These are necessary conditions and do not by themselves exclude a
whole cap on the eighth weight. Only the finite orbit calculation
is executable here; the geometric implication is written mathematics
using the previously proved rank-hole bounds.

    python3 orbit_replay.py
