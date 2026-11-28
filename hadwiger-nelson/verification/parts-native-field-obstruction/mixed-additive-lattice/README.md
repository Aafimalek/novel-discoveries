# The first mixed-field fixture is not a distance-two difference gadget

Let W be 0 and all sixth roots of unity, α=(√33+√−3)/6, and
β=(3+√−7)/4, with the indicated positive imaginary radicals.
This is exactly the staged candidate F=(W+W)+αW+βW, with marked
terminals 0,2. It has 931 distinct exact coordinate sites and
5,250 unit edges. A verified complete proper five-coloring
gives both marked terminals color zero. A separate explicit
solver-free witness shows its chromatic number is exactly three
and supplies two equal-terminal four-colorings. Thus this fixture
does not force their colors apart. There is no inference
about its full multiquadratic field or other fixtures.

## Exact method

Use the bitmask basis of Q(√33,√−3,√−7) with coordinate
denominator 24. The three square classes are independent:
primes 11 and 7 separate the first and third respectively,
and −3 is not a rational square. Thus coefficient comparison
is exact. Point generation agrees by two constructions:
explicit sparse coordinates for the three wheel factors,
and an independent multiplication-based construction from
the six powers of (1+√−3)/2 and all fourfold sums. This
checks completeness/deduplication and that the terminals
really are 0 and 2, with squared separation 4.

For every pair, compute the integer norm numerator of its
coordinate difference d using the positive constant
coefficient first. If it equals 576, check the full
d·conjugate(d) both by generic multiplication and by the
real five-line formula in the script. In the independent
model audit, the full real norm form is used on **every**
pair without the constant-coefficient sieve, and all
declared edges are independently checked by generic
multiplication. Both runs recover the same entire edge
set, not merely select listed edges. The checker assesses
the actual proper coloring on that complete graph,
reconstructing and evaluating all clauses as an additional
check.

The generated CNF fixes both terminals to 0 without loss
by color permutation, encoded with 4,655 variables and
36,493 clauses. A single Kissat 4.0.4 call found a complete
assignment. Under the guards, generation took 0.844 s,
the solver 0.009 s, and the independent audit 0.892 s.
No Lean or Git ran.

## Why the fixture is inherently too weak

The checked count 931 is exactly 19·7·7, so the map from
the three factor sites to their sum is injective. Changing
only one summand along a unit edge yields a distinct
Cartesian-product edge. The lattice ball W+W has 42 unit
edges, 14 in each of its three lattice directions (the
five row sizes are 3,4,5,4,3; sum row sizes minus one).
Each wheel has 12 unit edges, six spokes and six rim edges.
Thus the Cartesian edges alone number

    42·7·7 + 2·12·19·7 = 5250.

This equals the exact induced edge count, proving there
are **no mixed-summand unit edges**. The product structure
also yields two direct witnesses independent of SAT.
For ordinary three-coloring, take the triangular-lattice
color a+2b mod 3 in each factor's triangular coordinates,
and sum the three colors mod 3. Every unit edge changes
just one factor color by a nonzero residue. A unit triangle
in W+W with other coordinates zero proves the matching
lower bound: the fixture has chromatic number exactly
three. Recolor the two nonadjacent terminals with a fresh
fourth color to make them equal. Alternatively, encode each unrotated factor site by its two
triangular-lattice coordinates modulo 2, and color a site
by the sum in F₂² of the three factor colors. Each unit
edge changes exactly one factor and hence adds a nonzero
element of F₂². The terminals use underlying sites 0 and
2 in W+W and zero in each other factor, so they agree.
The software independently reconstructs the Cartesian edge
set, compares it with the full exact Euclidean set, and
checks all three explicit vectors and the unit triangle in
0.796 s. For a future field-mixing fixture, an inexpensive filter
is to check there are actually mixed-summand unit edges
before investing in coloring search. This is a heuristic
rejection screen for such plain products, not a prediction
of a genuine gadget.

## Replay

```sh
(ulimit -v 132000; timeout 59s python3 fixture.py generate NEW_DIRECTORY)
cmp NEW_DIRECTORY/exact-graph.json verified/exact-graph.json
cmp NEW_DIRECTORY/equal.cnf verified/equal.cnf
# Replay the existing positive witness without any solver.
(ulimit -v 132000; timeout 15s python3 fixture.py check NEW_DIRECTORY solver.out)
cmp NEW_DIRECTORY/checked-model.json verified/checked-model.json
(ulimit -v 132000; timeout 8s python3 product_witness.py NEW_DIRECTORY NEW_DIRECTORY/product-witness.json)
cmp NEW_DIRECTORY/product-witness.json verified/product-witness.json
```

Archived solver command used one process with
`timeout 14s kissat NEW_DIRECTORY/equal.cnf`. Hashes pin
both the graph and the witness.

The exact [full additive lattice proof](INFINITE-CARTESIAN.md) explains
why this is not just a feature of the finite patch. It rules out
all mixed-summand unit edges anywhere in the three-factor additive
group. See also the [paper PDF](additive-lattice-product.pdf).
