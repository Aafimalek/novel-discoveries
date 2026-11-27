# Size-17 Euler arrangements: low-profile double overlap

A low label has placement frequency two. This audit assumes minimum
frequency two and excludes cases with (a) no unused low pair sharing
two common used neighbors in a single other group, and (b) an unused
low pair sharing one common used neighbor in each of the two other
groups. It applies when a group specified in the manifest has at
least three lows. Each included native Kissat proof was independently
checked by DRAT-trim. This is not a Lean replay.

## Normalization

Choose a pair x,y as in (b), labeling x as group 0 label 0 and y as
group 1 label 2. Order the two words through x and the two words
through y so that the common group-2 neighbor occurs in the first
word of both. Normalize the x words to 0000 and 0111. In group 3,
the shared pair of positions cannot be (first x, first y): those
two words would repeat their group-2/group-3 projection. The other
three options give y words (1202,2220), (1201,2222), (1202,2221).
No word through y contains x, and its two group-0 labels are distinct,
so they can be fixed to 1 and 2 in order.

For each of groups 2 and 3, the union of the used neighbor sets
of x,y is precisely labels 0,1,2. Hence all nine cross-pairs of
labels 3,4,5 between groups 2 and 3 must be used, or one could add
a word combining x,y and an unused such pair. In particular,
those six labels have degree at least three. Requiring group 2 or
3 to have at least three lows is exactly requiring its labels 0,1,2
to have degree two. For a restricted anchor group 0 or 1, at least
three lows is equivalent to forbidding any four high labels,
encoded as one clause per four-element subset.

The CNF uses the same exact placement, frequency, maximality and
free-label symmetries as the zero-overlap audit. The overlap clauses
prohibit for each unused degree-two pair two common used neighbors
in any one other group. All clauses restricting the low count
are applied after the pinned diagrams, and are invariant under
permuting the reserved-free symbols, which preserves degree
sorting and incidence tie-breaking.

## Reproduce

```sh
python -m pip install python-sat==1.8.dev24
python verify.py --solve /path/to/kissat --checker /path/to/drat-trim
```

Use [Kissat 4.0.4](https://github.com/arminbiere/kissat/tree/rel-4.0.4)
and [DRAT-trim 2e3b2dc](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985).
The manifest records the exact DIMACS, proof, and replay SHA-256
hashes and proof sizes. Binary proofs are not bundled.

These six cases cover every arrangement satisfying the overlap
hypotheses with some group of at least three lows. If such a
group is an endpoint group of the selected unused pair, name
that endpoint x (group 0) before normalizing. If it is one of the
other two groups, name it group 2. In either choice the three
overlap diagrams remain exhaustive. There is no need to
separately pin a low profile in group 1 or group 3.
