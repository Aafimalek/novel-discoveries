# Size-17 Euler arrangements: high-profile double overlap

This audit excludes a subfamily only, specified by all of the following:
17 placements; minimum label frequency two; at least four labels of
frequency at least three in each of the four coordinate groups; an
unused pair of frequency-two labels sharing a used neighbor in **each**
of the other two groups.

The three normalized cases were independently DRAT-verified. Other
size-17 families, including instances in which there is no such
double-overlap pair, are outside the scope of this audit.

## Mathematical coverage

For an unused pair of degree-two labels, if there are two common used
neighbors in one other group, there are at least four labels unused with
both in that group and at least two in the fourth group. Maximality forces
all pairs between these two candidate sets to be used, so the latter
group has at least two labels of degree at least four. With at least four
high labels in that group, the excess over the baseline six degree-two
labels would be at least 2+2+1+1=6, contradicting 17−12=5. Thus each
overlap in the chosen double-overlap pair is exactly one.

Call the pair x in group 0 and y in group 1. Normalize the two words
through x to 0000 and 0111, and put y at label 2. A joint interchange
of the two anchor words makes the common group-2 neighbor label 0.
The common group-3 neighbor is then 0 or 1. The group's other neighbor
used with y is label 2. If both common neighbors are 0, they cannot be
paired together in a word through y because the (2,3) pair (0,0) was used
by 0000. If the common pair is (0,1) either pairing is allowed. These
are exactly the three cases for the two words through y:
`1202,2220`; `1201,2222`; and `1202,2221`.

The generators reserve the pinned labels and enforce the high-label
threshold by cardinality in each group. They do not prescribe the
number of high labels in the anchor group. Degrees are sorted on the
free suffixes. Among free labels of equal degree, lexicographic row
and column reordering of the used incidence matrices fixes ties:
choose the lexicographically least ordered list of matrices
(0,1), (0,2), (0,3) read by rows. A forbidden adjacent interchange
improves the first matrix it changes, while preserving all pinned
labels and earlier degree-order conditions. The rectangle implications,
pair injectivity, global count, and 1296 maximality clauses are as
described in the previous size-16 audit.

## Reproduce

```sh
python -m pip install python-sat==1.8.dev24
python generate.py double-same /tmp/case.cnf
python verify.py --case double-same --solve /path/to/kissat --checker /path/to/drat-trim
```

Use [Kissat 4.0.4](https://github.com/arminbiere/kissat/tree/rel-4.0.4)
and [DRAT-trim 2e3b2dc](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985).
For exact CNF and proof hashes and the size of the preserved original,
see `manifest.json`. Proof binaries are not bundled. The checked
stdout is in `replay/`. This is not a Lean replay.
