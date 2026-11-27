# Pair-packing bound for the max-148 integer case

**This is a partial formal exclusion, not the full 149 result.**
The formal reduction, strengthened quantitative bound and listed subsets
of the finite search are checked. A coverage module names the exact
remaining second-weight certificate obligation.

## Mathematical argument

A nine-weight integer list beginning with 148 has 512 centered signed
scores when all subset sums are distinct. They share one parity and can
be partitioned into 256 disjoint pairs ((z-148,z+148)).
Let (lambda=417600), (r=z\bmod592), and define
[
h(r)=\max(0,\min(\lambda,(592-r)^2,\lambda-(296-r)^2)).
]
Take (mu(z)=h(r)) if (r<296), and
(mu(z)=\lambda-h(r-296)) otherwise. Then (0\le\mu(z)\le\lambda)
and (mu(z)+\mu(z+296)=\lambda). For each distinct score z,
[
z^2\ge\mu(z)+\min(0,z^2-\mu(z)).
]
All negative terms vanish outside ([-646,646]). A finite kernel
calculation sums these terms on each parity: (-54,839,296) for even,
(-54,839,808) for odd. Because negative terms are nonpositive,
summing a subset cannot give a smaller sum than the full relevant
parity. Thus the square sum of the 512 scores is at least
(256\lambda-54,839,808=52,065,792). The signed-moment identity divides
this by 512 to give the verified weight-square minimum **101,691**,
replacing **87,381** for every max-148 branch.

## Checked source modules

* `PairPackingDual.lean`: the dual potential, both kernel arithmetic
  evaluations, and the bound on an abstract paired score list.
* `PairPackingWeights.lean`: transfer to ordinary natural subset sums
  and the max-148 search.
* `PairPackingWindowedCap.lean`: applies the existing checked
  terminal-window search with square threshold 101691.
* `PairPackingThirdSplit.lean`: a complete third-coordinate split for
  each fixed second-coordinate branch. Small closed checks are
  independent modules. Each checked split aggregator also proves the
  exact number of eligible third choices.
* `PairPackedCoverageXXX.lean`: the named contiguous coverage bound and
  a theorem conditional on all remaining second-coordinate checks.

The coverage theorem only uses `[propext, Classical.choice, Quot.sound]`.
Closed search decisions run in the kernel with `by decide +kernel`;
there is no `native_decide` or `sorry` in checked files. Use only the
sources reachable from the verified coverage module, not unsuccessful
work-in-progress shard attempts.

## Reproducibility

Use the repository's Lean / Mathlib versions (benchmarked with Lean
4.36.0). Add the modules to the repository's existing
`NineSeparatedSubsetSums` namespace. Build the latest verified
coverage module, e.g. `lake build NineSeparatedSubsetSums.PairPackedCoverage112`,
from the project root. Some coverage modules import the full existing
real reduction and require more memory than individual closed shard
modules; the 112 aggregator passed with Lean `-j 1 -M 3900`.

Locally, `run-checks.py` sequentially runs one Lean compilation at a time
and records exit status, wall time and maximum child RSS so far for that
invocation, assuming the dependencies are already compiled and
`LEAN_PATH` is set appropriately. The two generation scripts are not
trusted proof components: the generated Lean theorems check the
numeric data independently.

`bench.cpp` independently compares the two thresholds using the same
untrusted C++ recursive search. Build and run:

```sh
g++ -std=c++17 -O3 bench.cpp -o bench
./bench 87381 105 122
./bench 101691 105 122
```

On one local run, the old threshold visited 5,510,434 search states in
2657.4 ms; the new threshold visited 533,452 in 139.3 ms. At second=105,
states fell from 14,381 to 14. No witness was found in either measured
run. These timings and state counts are performance measurements, not
the Lean proof of the corresponding cases.

## Latest checked coverage

The canonical checked source manifest is `verified-sources.txt` (43 modules,
in build order). `PairPackedCoverage112.lean` proves all second-largest
weights through **112** excluded. The conditional real theorem
`separated_nine_at_least_149_of_remaining_pair_packed_through112`
states the only remaining obligation explicitly: the closed Boolean
shard check for each second-largest (113\le a\le147) is false.
The aggregate coverage check completed in 4.965s in this run. Individual
source decisions, including the cases 112 at offsets 9 and 10, are
documented in `checks.csv`, `split-checks.csv`, `final-112-checks.csv`,
and `coverage112.csv`. A resource-limit retry in the earlier CSV does
not count as an exclusion; both required retries subsequently passed
and are imported by the accepted aggregator.

## Experimental next step: certified four-point clusters

The separate `fourpoint-data.json` file contains compact symmetric
penalty tables for each second-largest weight 110–147 and both parities.
`python fourpoint_check.py fourpoint-data.json` performs an exact
integer-only replay; the floating-point LP generator is not part of
the trusted argument. These tables are **not imported into the checked
Lean coverage**.

Pair both largest weights. The 512 distinct scores become 128 disjoint
four-point clusters with values (c-148-a,c-148+a,c+148-a,c+148+a).
For each parity choose a nonnegative, finitely supported penalty `mu`;
certify that the sum of (z^2+\mu_z) for every cluster of that parity is
at least `lambda`. Each in-range center (c\in[-800,800]) is checked
exactly, using parity ((c+a)\bmod2=p). Outside that range the identity
[
\sum z^2=4(c^2+148^2+a^2)
]
verifies the lower bound using the nonnegativity of the penalties.
For distinct scores, the total penalty is at most the symmetric full
budget (mu_0+2\sum_{z>0}\mu_z).
The resulting stronger lower threshold on the weights' square sum is
(lceil(128\lambda-\mathrm{budget})/512\rceil). This recipe is
amenable to a small generic Lean interpretation theorem and closed
finite-constraint replay; until that implementation is checked,
the tables must not be counted toward further formal exclusions.
