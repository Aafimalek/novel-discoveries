# Size 17 is impossible for a maximal partial 36-officer arrangement

We encode an arrangement as a set of tuples from {0,…,5}⁴: each
coordinate is one of the four label groups, and no two tuples may
agree on two coordinates. Maximal means that every tuple has a
two-coordinate projection used by the arrangement. This compact
audit covers size 17; it does not on its own exclude lower sizes.
Together with the separate exclusion of all sizes below 17 and the
18-placement witness below, it gives minimum size 18. The 56 SAT
certificates were independently checked by DRAT-trim, not by Lean.

## Degree zero [analytic]

If a coordinate group has a zero-degree label, take the tripartite
graph of missing pairs on the other three groups. A triangle would
give an extension using the zero-degree label; thus the graph is
triangle-free. Each vertex v has equal missing degree e(v) to each
other group, namely six minus its placement degree. For each missing
edge uv, the missing neighbors of u and v in the third group are
disjoint, so e(u)+e(v)≤6. Between a fixed pair of groups there are
M=36−17=19 missing edges. Summing along those edges gives the sum of
the degree squares on both sides at most 6M. Cauchy gives a lower
bound 2M²/6 for the same sum, so M≤18, a contradiction.

## Degree one [checked]

All 27 normalized cases in [degree-one](degree-one/README.md) were
excluded. The reduction and exact clause construction are
documented there.

## Degree two [checked]

All four groups contain a low, a degree-two label; otherwise a group
would have degree sum at least 18. An unused low-low pair may have
shared used neighbors in the two remaining groups. The following
case selection is exhaustive.

1. If all low-low pairs are used, an incidence argument forces one
   low per group, all in one word. [Seventeen normalized patterns](all-low-pairs-used/README.md)
   of their four other words are excluded.
2. Otherwise, if any unused low-low pair has two common neighbors in
   one other group, a forced candidate rectangle rules out any
   overlap in its opposite group. The
   [single normalized diagram](two-neighbors-one-group/README.md)
   is excluded.
3. Otherwise, if some unused low-low pair has a common neighbor in
   each remaining group, there are three normalized overlap diagrams.
   If all groups have at least four labels of degree≥3, the
   [three high-profile formulas](two-groups-high-profile/README.md)
   are excluded. In any other profile, some group has at least three
   lows. Choose it as group 0 if it is among the two selected lows'
   groups, or as group 2 otherwise. The
   [six low-profile formulas](two-groups-low-profile/README.md)
   are excluded.
4. Otherwise, if some unused low-low pair has exactly one common
   neighbor, the
   [single-overlap formula](single-overlap/README.md)
   is excluded.
5. Otherwise some unused low-low pair exists and no unused low-low
   pair shares a neighbor. The [zero-overlap formula](zero-overlap/README.md)
   is excluded.

Higher minimum degree is impossible at size 17. These are all
cases.

## The upper witness

For c=0,1 and a,b in the field F₃, take

```text
(3c+a, 3c+b, 3c+(a+b mod 3), 3c+(a+2b mod 3)).
```

Within each c-block, any two of the four linear forms in a,b are
independent over F₃, so all projected pairs in that block occur
exactly once. Different blocks use disjoint labels in each group.
Any proposed additional word has at least two labels from one
block and hence an already-used pair. The 18 words and independent
maximality/injectivity test appear in the accompanying files.

## Relation to prior work

Donovan, Grannell and Yazıcı already gave the order-six upper bound
18 in Table 1 of [On maximal orthogonal partial Latin squares and
minimal codes with specified length, minimum distance and covering
radius](https://doi.org/10.1007/s10623-025-01704-x) (2025). That paper
establishes exactness for orders four and five in the table, not for
order six. Their [subsequent general lower bound](https://arxiv.org/abs/2602.09908)
is n²/3 and gives exact minima for n≥21; it gives 12 when n=6.
The work here certifies the missing lower bound for order six.

## Audit

Each case-family directory has exact CNF generation, checker
output, and SHA-256/size manifests. Proof binaries are not bundled.
Use its README to regenerate them with Kissat 4.0.4 and verify
them with DRAT-trim at 2e3b2dc. The scripts use
`python-sat==1.8.dev24`. Large proofs may need a disk-backed
temporary directory (`TMPDIR`).
Run `python check_generators.py` to regenerate all 56 DIMACS inputs and validate their hashes and the archived checker-log hashes without solving.
