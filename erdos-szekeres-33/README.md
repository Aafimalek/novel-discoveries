# Erdős–Szekeres at 33 points

**Open.** The aim is to prove that 33 points in the plane with no three collinear contain seven in convex position, or find a genuine real counterexample. [Bogdan](https://arxiv.org/abs/2512.24061) and [Baek–Balko](https://doi.org/10.1016/j.jcta.2026.106195) address narrower formulations.

The Lean theorem `ES33.geometric_counterexample_gives_signotope` chooses a shear separating the horizontal coordinates, sorts the points, and sends a counterexample to a Boolean assignment satisfying the ordered quadruple and seven-point clauses. `ES33.es33_of_clause_unsat` makes this sufficient for a proof if the abstract relaxation is UNSAT. A SAT assignment would not by itself supply a realizable point set.

`LocalCNF.lean` verifies the compact eight-clause encoding per quadruple against all 32 possible local Boolean inputs. The 33-point instance has 46,376 Boolean variables and 4,599,408 clauses. Code generates numbered DIMACS; the serialization is not yet linked to Lean. The controls were 8/5 SAT and 9/5 UNSAT, with the latter trace independently replayed. No SAT/UNSAT result is claimed for 33/7.

Run `lake build` from `lean/` with the pinned toolchain. The checked geometric bridge uses only the standard Lean axioms. See the script's argument help for numbered DIMACS generation.
