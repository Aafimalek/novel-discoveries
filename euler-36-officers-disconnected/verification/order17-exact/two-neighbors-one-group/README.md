# Size-17 Euler arrangements with two common neighbors

This audit excludes the following subfamily: maximal arrangements of
17 placements, minimum label frequency 2, and an unused pair of
degree-two labels in distinct groups with two common used neighbors in
another group. It imposes no additional global frequency-profile
restriction. A native Kissat proof was independently checked by
DRAT-trim, whose checked output is archived here. This is not a Lean replay.

## Coverage

For an unused degree-two pair x,y with two common used neighbors in
a third group, the set of labels unused against both in that group has
size 4. If they shared any common used neighbor in the fourth group,
there would be at least 3 labels unused against both in that group.
Maximality would force all pairs in the resulting 4×3 rectangle to be
used. Three labels would have degree at least 4, exceeding the group’s
available frequency excess 17−6·2=5. Thus the fourth-group degree-two
neighborhoods of x and y are disjoint.

Put x at (group 0, label 0), y at (group 1, label 2), and the two words
through x at 0000 and 0111. The neighbors of y are the same labels
0 and 1 in group 2 and two fresh labels in group 3. By naming those
fresh labels 2 and 3, and the other group-0 values of y's words 1 and
2, the two words through y are 1202 and 2213. The four group-2 labels
2,3,4,5 must all pair with the two group-3 labels 4,5 by maximality.
These eight used pairs and their degree implications are in the CNF.
The free labels 4,5 in group 3 may be sorted by frequency.

The common rectangle-degree clauses and possible overlaps in any
other degree-two pair are subject to the same 4×3 excess test. The
base model enforces pair injectivity, exact cardinality and degree
thresholds, and maximality. Equal-degree free rows and columns can be
sorted by lexicographically minimizing the ordered list of used
incidence matrices (0,1),(0,2),(0,3) while fixing pinned values and
preserving degree order, as in the size-16 audit.

## Reproduce

```sh
python -m pip install python-sat==1.8.dev24
python generate.py q2 /tmp/q2.cnf
python verify.py --case q2 --solve /path/to/kissat --checker /path/to/drat-trim
```

Use [Kissat 4.0.4](https://github.com/arminbiere/kissat/tree/rel-4.0.4)
and [DRAT-trim 2e3b2dc](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985).
The exact DIMACS, original proof, and replay-output hashes are in
`manifest.json`. The proof binary is not bundled. Other branches
implemented in the source are outside this audited claim.
