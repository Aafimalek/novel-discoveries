# Size-17 Euler arrangements with only single-neighbor overlap

This audit excludes maximal arrangements of 17 placements with minimum
frequency two in which some unused degree-two pair shares a used
neighbor, and no unused degree-two pair shares multiple used neighbors
in total. No other frequency-profile restriction is needed. The native
Kissat proof was independently checked by DRAT-trim. This is not a Lean
replay.

## Normalization and conditions

Choose an unused pair x,y of degree-two labels with a common used
neighbor. Set x to group 0 label 0, y to group 1 label 2, and set the
shared neighbor's group to group 2. Of the two words through x,
put the shared neighbor in the first, labeled 0000, with the
second labeled 0111 by pair injectivity. Put the shared neighbor
in the first word through y, where y's group-0 label is different
from x. Normalizing new labels independently now gives the two
words through y as 1202 and 2223. There is a forced used 3×2
rectangle between the candidate labels 3,4,5 and 4,5 in groups
2 and 3, respectively, or one could add an unused word.

The no-multiple-overlap clauses follow directly from the branch
hypothesis: for every unused degree-two pair, it is forbidden (a)
to have two distinct common used neighbors in either other group,
or (b) to have one common used neighbor in each other group. These
conditions and the degree thresholds are label-invariant; the
pinned words are not affected by free-label degree sorting and
tie-breaking incidence rows/columns as in the size-16 audit.

## Reproduce

```sh
python -m pip install python-sat==1.8.dev24
python generate.py one /tmp/case.cnf
python verify.py --case one --solve /path/to/kissat --checker /path/to/drat-trim
```

Use [Kissat 4.0.4](https://github.com/arminbiere/kissat/tree/rel-4.0.4)
and [DRAT-trim 2e3b2dc](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985).
The exact DIMACS, proof, and replay-output hashes appear in
`manifest.json`; no proof binary is bundled.
