# Euler 36 officers: certifying the exclusion of exactly 16 placements

**Result and scope.** Let a placement be a 4-tuple of labels in `{0,…,5}`, one each
from the row, column, rank, and regiment groups. A valid partial arrangement
does not repeat any two-group projection; it is maximal if no new tuple can be
inserted. The ten cases below exclude **exactly 16** placements. In conjunction
with the earlier repo proofs excluding ≤15 and its explicit 18-placement
maximal construction, this gives **17 ≤ the minimum ≤ 18**. The size-17 decision
and an end-to-end Lean replay are *not* established by these files.

This is a mathematical reduction plus independently replayable SAT
certificates, not a claim of a handwritten proof of UNSAT. It uses the
earlier repo's disconnected minimum of 18 and its published lower-bound
method, not any unchecked search claim. Experiments on size 17 are separate.

## Prior ingredients

* The base encoding is copied verbatim as `base.py` from
  `Aafimalek/novel-discoveries/euler-36-officers-disconnected/verification/verify_certificates.py`,
  Git blob `d8b69095e57325f98365d266c6b35e9cf7db39f3`. The reduction uses the
  same SAT model and elementary degree bounds. The only change to
  `anchored_base.py` is to allow a larger reserved prefix when degree-sorting
  free labels, i.e. to turn off some original sorting constraints.
* The prior disconnected theorem says that a maximal arrangement whose
  used-pair graph is disconnected has at least 18 words. Graph vertices
  are all 24 labels; edges are the used pairs.
* For a frequency-zero label, the matching argument of
  [Donovan–Grannell–Yazıcı, Theorem 2.1](https://arxiv.org/abs/2602.09908)
  gives `2F ≥ 6²`, so F=16 is impossible with minimum frequency zero.
  Equivalently, projection onto the other three groups would be a maximal
  order-six partial Latin square. The average frequency per group is 16/6,
  so the minimum frequency `m` is 1 or 2.

## Variables and common constraints

Let `W[u]` record a placement, `P[x,y]` a used pair of labels in distinct
groups, and `D[x,d]` the proposition that label x has frequency at least d.
For every pair, `P` is equivalent to the disjunction of its supporting
`W` variables, at most one being allowed true. Thus the count of true pairs
in any one projection is the number of placements. Enforce 16 placements
by counting the first projection. A word can be inserted iff all six pairs
are unused, so append the clause “at least one of its six pairs is used” for
each of the 1296 words. Frequency is the number of incident used pairs in
any fixed other group; base's exact Boolean truth table enforces all used
degree thresholds and the normalized minimum. Counting the thresholds above
m in each group gives `16 − 6m`, since a label of frequency d contributes
exactly d−m thresholds. The encodings may enforce this redundant equality
separately. If a selected word has all four endpoint frequencies equal to
one, it is an isolated component in the used-pair graph, contradicting the
earlier disconnected bound. Each word gets the clause excluding this case.

### Rectangle constraints

For an unused pair x,y, in each of the other two groups the labels unused
with **both** x and y form a candidate set. The product of the two candidate
sets must have all cross pairs used, since any unused cross pair would give
an insertion. If `d(x)≤a`, `d(y)≤b`, each candidate set has size at least
`r=6−a−b`. Consequently, when r>0, each remaining group has r labels of
degree at least r, and base's cut `F≥r²+(6−r)m` is necessary. For any
specified candidate z in one group, `d(z)≥6−a−b`; if some specified label
in the other group was used with both x and y, inclusion-exclusion improves
this to `d(z)≥7−a−b`. The new conditional CNF clauses express these
implications only under the relevant unused pairs, degree bounds, and
common-neighbor premises.

The stronger m=2 versions in the `lowpair` and wedge formulas also use:
if an unused d=2 pair x,y shares at least two used neighbors in one remaining
group H, H has at least four candidate labels; if it shares even one in the
other group K, K has at least three candidates. The required 4×3 rectangle
forces excess at least `3·(4−2)=6` in group K, more than the available
four. Even without the additional common neighbor in K, K has at least two
candidate labels of degree at least four. If every group has at least
`p≥3` labels of degree at least three, these two degree-four labels and
the other p−2 high labels would require excess `4+(p−2)>4`. Therefore the
two-common-neighbor configuration is impossible already in H if p≥3.
For p=2, only the combination of two in H and one in K is forbidden.

## The case m=1

Normalize one degree-one label to label 0 in group 0, and the unique
placement through it to `(0,0,0,0)`. All other label permutations act
independently across the four groups, and sorting the unpinned labels by
frequency imposes no restriction (the "minimum label 0" setting and the
normalized word are unaffected).

Fix any two nonanchor groups i,j. Restrict their pair matrix to nonzero
labels, and take a maximum matching of unused pairs in the 5×5 matrix, of
size t. Each matched unused pair (u,v) must block all five nonzero labels
in the fourth group via used pairs incident to u or v, since the degree-one
anchor is unused against all those labels. Thus `d(u)+d(v)≥5` for each
matched pair. Pair the unmatched rows and columns arbitrarily. Every
unmatched row–column pair is used (else augment the matching); for a chosen
unmatched row and column plus any matched edge, at least one of the two
cross pairs to that matching edge is used (else replace that matching edge
with two). Thus each unmatched pair has degree sum at least
`2(5−t)+t=10−t`. Summing over the five paired rows and columns gives
`2F−d_i(0)−d_j(0) ≥ 25+(5−t)² ≥ 25`. Encode the weaker inequality by
forbidding both anchored degree thresholds whenever their sum exceeds
`2F−25`.

If t=5, each nonzero fourth-group label z must block all five matched cells
by occurring in the row or column of each cell. Each occurrence of z
can block at most two such cells (one by row and one by column), so
`d(z)≥3` and the five nonanchor labels contribute at least 15 to the
fourth-group frequency total. Its anchor therefore has degree at most
`F−15`. For each of the five-element column permutations, encode “if the
fourth-group anchor degree is >F−15, at least one of the corresponding
five matrix positions is used.” This proves the matching clauses.

## The case m=2: profile normalization and coverage

Every group has excess four above the six degree-two labels. Let p be
the least number of high labels (degree ≥3) in any group; choose group 0
to attain p. Then `1≤p≤4`. The positive parts of the excess partition
are respectively `(4)`, `(3,1)` or `(2,2)`, `(2,1,1)`, or
`(1,1,1,1)`. Thus the possible pairs (p,h) with h the highest degree in
group 0 are exactly `(1,6),(2,5),(2,4),(3,4),(4,3)`.

For high anchors: choose one highest-degree label in group 0 as label
5, and choose a degree-two label as label 0. Relabel the h words via 5
as `(5,a,a,a)`, `0≤a<h`; each projection through 5 uses distinct labels
by linearity. Remaining unpinned labels sort by degree; the h aligned
labels may be permuted jointly across groups 1–3 to sort their
frequencies in group 1. Group 0 has labels `6−p,…,5` high, the other
labels low, and all groups have at least p highs. This normalization is
used directly for profiles (1,6), (2,5), (2,4), (3,4).

The low-pair clauses in (2,4) and (3,4) may additionally demand an unused
pair between label 0 of group 0 and some degree-two label y in group 1:
group 0 has at least three lows, group 1 has a low by its average,
and y of degree two cannot be used with every low of group 0. Choose
one of the lows missed by y as label 0; this choice does not affect the
selection of the high anchor, and the new witness condition only asserts
existence of y regardless of its eventual numbering.

### Tie-lex clauses

In the stronger branches, within each already degree-sorted free
suffix compare adjacent *equal-frequency* labels by their used-pair
incidence vectors. For group 0 the comparison is between rows of
its matrix against group 1; for group j>0 it is between columns of
the corresponding matrix against group 0. Reserve all label positions
pinned by normalized words and the minimum-degree anchor. In particular,
the high-anchor group-0 comparisons exclude label 5. Take the
lexicographically least list of pair matrices `(0,1),(0,2),(0,3)`,
read row by row, over relabelings consistent with all other symmetry
constraints. Swapping two adjacent tied free rows would improve the
first matrix iff their vectors violated the ordering. Swapping tied
free columns changes only the corresponding matrix, and its first
changed entry lies at the first row where the two column vectors
differ; a forbidden order would improve that matrix. Such swaps fix
all anchors, preserve their joint degree-ordering, preserve any
degree/equality patterns, and preserve the labeled low-pair condition
because it pins only group-0 label 0 and is existential in group 1.
These independently show that the enumerated equal-prefix
first-difference clauses are simultaneously sound. Fixed-prefix wedge
cases exclude all pinned labels from the tie comparisons.

### Last profile (4,3): five small cases

Here all four groups have exactly two low labels of degree 2 and four
labels of degree 3. If all low-low distinct-group pairs were used, each
low label would have both neighbors low in each other group, disconnecting
all lows from highs. Thus there exists an unused low-low pair. The
rectangle count above implies it shares at most one used neighbor in
each remaining group.

If a pair shares exactly one used neighbor in **both** remaining groups,
choose such a pair. Put x at group-0 label 0, y at group-1 label 2; its
unused relation with x means y is outside the two group-1 labels already
used by x. Normalize the two words through x to
`(0,0,0,0),(0,1,1,1)`. A joint interchange of these two anchor words
makes the common group-2 neighbor label 0. In group 3 the common label
is 0 or 1. Label the unique neighbors of y outside the x-neighborhoods
in groups 2 and 3 by 2. In the common-(0,0) case, y's two words cannot
pair these common labels together because that would repeat the (2,3)
pair of the first x-anchor word, so there is one crossed case. In the
common-(0,1) case there are two pairings. Give y's other two group-0
neighbors labels 1 and 2 in the order of the listed words:
* `same`: `(1,2,0,2),(2,2,2,0)`;
* `cross1`: `(1,2,0,1),(2,2,2,2)`;
* `cross2`: `(1,2,0,2),(2,2,2,1)`.

If **no** unused low-low pair shares a neighbor in both groups, choose
any unused low-low pair; it has either zero shared neighbors, or exactly
one in just one group. Permute groups 2 and 3 so the one shared neighbor,
if present, is in group 2. Again fix the x words and y=2 in group 1;
all new labels can be independently named in the pinned y words. Cases:
* `zero`: `(1,2,2,2),(2,2,3,3)`;
* `one`: `(1,2,0,2),(2,2,2,3)`.

Include the global no-double-overlap clauses only in these last two
cases. With the pinned labels, enforce the number of high labels in
group 0 by a cardinality constraint, **not** by assuming labels 1 and
2 have prescribed degrees. Free suffixes are degree- and tie-sorted
only after all pinned labels. Earlier exploratory versions of these
cases (before this correction) are not evidence; use only the formulas
with prefixes `wedgefinal` and `nodouble`.

## Exact artifacts and reproduction

`cases16.tsv` maps case ID to DIMACS stem and checked gzipped proof name;
`F16.sha256` gives SHA-256 hashes of every DIMACS and compressed proof.
All named cases had `s VERIFIED` on independent DRAT-trim. Some older
exploratory logs say UNSAT but have incomplete traces: **only case-manifest
artifacts are part of this claim.**

Requirements: CPython 3.10 or newer, `python-sat==1.8.dev24`, and
[DRAT-trim source at commit 2e3b2dc](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985).
`regen16.py` loads the source file for the relevant formula, executes its
CNF construction only, and writes DIMACS without invoking any SAT solver.
Required source files: `base.py`, `anchored_base.py`, `certify.py`,
`split.py`, `lowpair.py`, `wedgefinal.py`, `nodouble.py`, `regen16.py`.

```bash
cd /tmp/euler-dot
# PYTHONPATH=/tmp/euler-py here contains pinned python-sat; omit if installed.
sha256sum -c F16.sha256
work=$(mktemp -d)
while IFS=$'\t' read -r case stem packed; do
  PYTHONPATH=/tmp/euler-py python regen16.py "$case" "$work/$case.cnf" || exit
  cmp "$work/$case.cnf" "$stem.cnf" || exit
  gzip -dc "$packed" > "$work/$case.drat" || exit
  ./drat-trim "$work/$case.cnf" "$work/$case.drat" -q > "$work/$case.log" || exit
  grep -qx 's VERIFIED' < <(tr -d '\r' < "$work/$case.log") || exit
  printf '%s VERIFIED\n' "$case"
  rm "$work/$case.drat"
done < cases16.tsv
```

To regenerate a raw DRAT proof rather than replay the preserved one, use
Kissat release 4.0.4 against a regenerated DIMACS, for example
`kissat generated.cnf fresh.drat` (exit status 20 is UNSAT). Do not require
byte-identical solver output; DIMACS regeneration is byte-for-byte and
every proof must independently replay. The archived proof variants use
both CaDiCaL195 and native Kissat, trimmed when helpful.

## Separate size-17 work

No 17-placement maximal witness is known from these runs. Heuristic and
bounded exact neighborhood searches are not exhaustive obstruction proofs.
Candidate size-17 proof branches and solver logs are separate from the
above ten cases and must not be merged into this conclusion.

## SHA-256 manifest (inline copy)

```text
bc5ecb011c0147871b33a13a5cf64b9417c330d9f47ee0604634ae3510c586a1  exact-f16-m1.cnf
c99bfbc7586655bfc93aee5357eee40e42aa13ea09353c8b6a0aea03b5f0fa5f  exact-f16-m1.trim.drat.gz
652924df5773b8f9d8083758e7a2f1a81583d2819697ad50b0c49738a5e788d7  proof-f16-m2-1:6.cnf
969cc61af6abae9bfcc166acd2c8df44d3dc3017713fa26019fda0c415ac59ff  proof-f16-m2-1:6.trim.drat.gz
babcaf34f0994755e36ce951effa082578c416b9053bff69799e867abb3ad8fc  proof-f16-m2-2:5.cnf
ced0ed8df4504cf1d0feccf4ce34937e7748a94c2e35db496c09c2063a6296fd  proof-f16-m2-2:5.trim.drat.gz
5743bc432fcaff90c15ddf8576fad413b5e482289a4dc28c5587898b7b64c96c  lowpair-f16-m2-2:4.cnf
4876149ba04107813ef12fee2bb01c9e93d132c3df3f20e12d0a54118f9a59a7  lowpair-f16-m2-2:4.kcore.drat.gz
405dc6d865b6b2bd35fd017cc85df17bf1ad046c3717ca182a4874904d8fbbaf  lowpair-f16-m2-3:4.cnf
e71cca684aeffc6aaa2f5b40fbe2566449e73e200fa204721dc24797d4776e7c  lowpair-f16-m2-3:4.trim.drat.gz
941bc3103face07cdfdefd0487299e62a57b6c7d8e8417a03a17fc253d5e771e  wedgefinal-f16-m2-4:3-same.cnf
39264d86fd587ba763832109b16034bd6deb80c1bdd797b0679ded3a45f844e3  wedgefinal-f16-m2-4:3-same.ncore.drat.gz
07a7606356a15dc40f947a8600d095f29d4b20c5255320daa27ff3238b9fa39d  wedgefinal-f16-m2-4:3-cross1.cnf
abeea0062d1fad3c0169217bfc8489feeb2644344b6726f807639718a68f1708  wedgefinal-f16-m2-4:3-cross1.ncore.drat.gz
065ab33cc8b76866a6dc223dcd95f076b1fb1881fab606d182aa0ef920b66d42  wedgefinal-f16-m2-4:3-cross2.cnf
d18e132cee728f8821ff5a62a0c400abb75903dcfe4f09b11443f5c9b92f592b  wedgefinal-f16-m2-4:3-cross2.trim.drat.gz
c515258a096f5f0c6f6ba3ad16fc923a3e919a6461eaed643ccbd8ed39558b00  nodouble-f16-m2-4:3-zero.cnf
c0fd5a7b6408a1e62d12302039da5b132480ec60371e50a4e873dcde93567add  nodouble-f16-m2-4:3-zero.trim.drat.gz
dfe18753f54b57cc9659810265237097eb48e88db0bccaf30e411b94332ecc40  nodouble-f16-m2-4:3-one.cnf
ae9c44644c0017992d1c17c1b841042e00fe88dbfba9cccb509613ec0c188323  nodouble-f16-m2-4:3-one.ncore.drat.gz
```
