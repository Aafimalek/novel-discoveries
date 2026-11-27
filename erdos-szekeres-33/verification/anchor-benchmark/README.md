# A 32-label residual problem for Erdős–Szekeres at 33 points

The Lean theorem `ES33.es33_of_residual_unsat` reduces the exact
planar 33-point problem to excluding a 32-label signotope with both:
1. no seven-set whose ordered four-subsets all have even orientation parity;
2. no six-set whose ordered triples all have positive orientation.

This is a proof of the mathematical reduction, **not** a proof that the
residual problem is unsatisfiable. A satisfying abstract sign assignment
need not be realizable by points. No new Erdős–Szekeres bound is claimed.

## Lean proof

- [`ProjectiveAnchor.lean`](../../lean/ES33/ProjectiveAnchor.lean) uses a
  finite projective chart. First shear and sort, then translate the
  leftmost point to zero and order the other points by slope. The map
  `(x,y) ↦ ((y+C*x)/(x+e), -x/(x+e))` for one sufficiently small positive
  `e` preserves every orientation sign up to reindexing. Its x-order
  agrees with the slope order, and every sorted triple through the new
  first point has positive orientation. The normalization is known:
  see [Subercaseaux et al., ITP 2024, §5](https://doi.org/10.4230/LIPIcs.ITP.2024.35).
  The cited formalization uses a point at infinity as an intermediate
  step; this implementation stays finite.
- [`AnchorReduction.lean`](../../lean/ES33/AnchorReduction.lean) proves
  the abstract equivalence. In a sorted quartet containing the anchor,
  three orientations are positive and the remaining orientation is the
  residual triple. The packet constraint is automatic. A seven-set
  containing the anchor is thus convex in the parity model exactly
  when its residual six-set is a cup.
- [`AnchoredTarget.lean`](../../lean/ES33/AnchoredTarget.lean) links these
  steps to the actual geometry. Lean 4.36.0 with Mathlib
  `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` checks the whole reduction
  with only `propext`, `Classical.choice`, and `Quot.sound`.

## Experimental DIMACS

The [published Baek–Balko generator](https://github.com/jcpaik/erdos-szekeres-sat/blob/61bfbd6f04d73865a5037b0a416d5ba18ce34fbd/lib/erdos.py)
can encode the residual instance as `etv_signotope(7,7,6,32)`. The second
argument bans a 7-cap; the third bans a 6-cup. This input has **37,365
variables and 474,144 clauses**, compared with 45,210 and 570,880 for
the unanchored endpoint encoding. The exact hashes are in
[`generation.tsv`](generation.tsv). The numbered generator and its
complete correctness are not part of the Lean proof.

Use the published generator through the adjacent endpoint benchmark's
pinned, hash-checking fetch program. No upstream source is included here.

```sh
(cd ../endpoint-benchmark && bash fetch_upstream.sh)
python3 generate.py ../endpoint-benchmark/upstream
python3 benchmark.py /path/to/kissat | tee results.tsv
python3 check_positive.py ../endpoint-benchmark
/path/to/drat-trim anchor-5-8.cnf anchor-5-8.drat
```

The positive control audit checks every CNF clause, legal packet, the
convexity avoidance condition, and the additional shorter-cup ban.
The negative pentagon control has an independently verified DRAT trace.
The historical 17-point threshold itself is known: see
[Marić's Isabelle/HOL verification](https://doi.org/10.1007/s10817-017-9423-7).

## Observed results

| Residual labels | Forbidden polygon / cup | Result | Local wall time |
| ---: | :---: | :--- | ---: |
| 7 | 5 / 4 | SAT | 0.006 s |
| 8 | 5 / 4 | UNSAT; DRAT checked | 0.018 s |
| 15 | 6 / 5 | SAT | 0.116 s |
| 16 | 6 / 5 | UNSAT (solver result) | 162.356 s |
| 32 | 7 / 6 | No result within time limit | 120.009 s |

Measured with Kissat 4.0.4. The two SAT controls were audited
independently. The 16-label result calibrates against the established
17-point theorem; the 32-label search is unresolved. Times are
single-run observations, not an estimate of speedup.
