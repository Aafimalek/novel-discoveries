# Erdős–Szekeres at 33 points: formally justified compact SAT reduction

The open target is whether every 33-point real planar set in general position
contains a subset of seven points in convex position. A convex polygon is not
required to be empty. The classical construction gives the lower bound 33.
This repository does not prove the 33-point conjecture or give a counterexample.

## Checked statements

- `lean/ES33/QuadrupleReduction.lean`: planar Carathéodory implies a nonvertex lies in the
  hull of at most three other points. For a set of size at least four, convex
  position is equivalent to convex position on all four-subsets.
- `lean/ES33/TriangleOrientation.lean` and `lean/ES33/QuadrupleParity.lean`: actual real convex hulls
  are connected to signed triangle determinants. A general-position four-set is
  nonconvex exactly when its four determinants have odd sign parity.
- `lean/ES33/OrientationClauses.lean`: on a fixed real realization, no convex heptagon is
  equivalent to the clause saying each seven-set has a nonconvex four-subset.
- `lean/ES33/Signotope.lean` and `lean/ES33/FullReduction.lean`: the orientation packet
  `abc, abd, acd, bcd` for four left-to-right points changes sign at most once.
  An orientation-preserving shear and relabeling put every input set in this
  order. Therefore every geometric counterexample yields a satisfying assignment.
- `lean/ES33/LocalCNF.lean`: eight ternary clauses implement the packet rule and parity bit
  exactly. This module proves the final conditional statement
  `es33_of_compact_clause_unsat`: excluding every assignment to the abstract
  compact clause family would resolve the 33-point case positively.

All modules were checked with plain Lean 4.36.0 against Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Printed axiom audits use only
`propext`, `Classical.choice`, and `Quot.sound` where needed. There is no
SAT result for 33 points and no formal bridge from the typed family to the
numbering of the generated DIMACS text yet. SAT in this relaxation would
in general not imply real geometric realizability.

To build from the project directory, with networking enabled:

```sh
cd lean
lake exe cache get
lake build
```

## Exact local encoding and controls

The generator `verification/signotope_cnf.py` reproducibly assigns IDs to all sorted triples
and all sorted quadruples. Its compact local truth table was found by the
exhaustive prime-implicate, set-cover program `verification/optimize_local.py`, and
its equivalence against all 32 local rows is checked in Lean. The baseline
enumerates packet exclusions and parity exclusions separately.

| 33-point encoding | Variables | Local clauses per four-set | Total clauses | Literals per seven-set clause |
| --- | ---: | ---: | ---: | ---: |
| Compact | 46,376 | 8 | 4,599,408 | 35 |
| Baseline | 46,376 | 24 | 5,254,128 | 35 |

The exact count of seven-subsets is 4,272,048. Thus even the compact encoding leaves
a large solve. Using Kissat 4.0.4 and independent DRAT-trim, the standard small
controls were satisfiable for eight points avoiding a convex pentagon, and
unsatisfiable for nine points avoiding a convex pentagon. The latter proof log
was accepted as `s VERIFIED`. These controls are not new Erdős–Szekeres bounds.

```sh
python3 optimize_local.py
python3 signotope_cnf.py 8 5 es8.cnf
kissat es8.cnf
python3 signotope_cnf.py 9 5 es9.cnf
kissat es9.cnf es9.drat
drat-trim es9.cnf es9.drat -q
# Write the full experiment input; uses substantial storage.
python3 signotope_cnf.py 33 7 es33.cnf
```

## Primary background

- [Erdős and Szekeres, lower-bound construction](https://www.renyi.hu/~p_erdos/1960-09.pdf).
- [Bogdan, *Notes on the 33-point Erdős–Szekeres problem*](https://arxiv.org/abs/2512.24061)
  establishes the geometric four-set approach and reports UNSAT for restricted anchored instances.
- [Baek and Balko, *The Erdős–Szekeres conjecture revisited*](https://doi.org/10.1016/j.jcta.2026.106195)
  establishes the conjectured threshold for restricted decomposable sets and for split polygons,
  not for arbitrary general-position point sets.

## Checked one-point extensions

The [one-point extension audit](verification/extension32) gives one explicit integral 32-point configuration with no convex heptagon and independently replayed refutations for all 33 insertion slots of one more point. This rules out extending this sign type, not all possible 33-point configurations. The bundle includes the original coordinates, formula generator, independent hull check, exact hashes, and all 33 compact proof certificates.
