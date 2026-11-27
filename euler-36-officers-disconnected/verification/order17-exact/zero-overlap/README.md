# Size-17 Euler arrangements with no low-pair overlap

This audit excludes maximal arrangements of 17 placements with minimum
label frequency two that have an unused pair of degree-two labels but
no common used neighbor of any such unused pair. There is no further
frequency-profile restriction. The generated native Kissat proof was
independently checked by DRAT-trim; its checked output is included.
This is not a Lean replay.

## Coverage

Choose an unused pair x,y of degree-two labels in distinct groups and
name them (group 0, label 0) and (group 1, label 2). Normalize the two
words through x to 0000 and 0111. In each of groups 2 and 3, the two
neighbors of y are disjoint from x's two neighbors: otherwise x,y would
have a common used neighbor. Hence the words through y can be relabeled
to 1222 and 2233. No such word contains x, and their group-0 neighbors
are different by pair injectivity. The unpaired labels 4 and 5 in groups
2 and 3 give a 2×2 rectangle of pairs that must all be used by maximality.

The CNF enforces the global no-common-neighbor condition: for each unused
pair of labels of degree exactly two, and for each label in either other
group, the two corresponding pairs cannot both be used. Every condition
is expressed by its direct implications between pair variables and
degree thresholds. The usual degree-sorting of free labels and
lexicographic tie-breaking in used incidence matrices preserve pinned
values and this unlabeled condition (as in the size-16 audit).

## Reproduce

```sh
python -m pip install python-sat==1.8.dev24
python generate.py zero /tmp/case.cnf
python verify.py --case zero --solve /path/to/kissat --checker /path/to/drat-trim
```

Use [Kissat 4.0.4](https://github.com/arminbiere/kissat/tree/rel-4.0.4)
and [DRAT-trim 2e3b2dc](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985).
The exact DIMACS, proof, and replay-output hashes appear in
`manifest.json`. No proof binary is bundled. Cases with no unused
degree-two pair, or an unused pair with a shared neighbor, are outside
this audit.
