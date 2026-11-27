# Kernel UNSAT proof for the entire numbered rightmost-insertion formula

This is a bounded pilot for **slot 32 only**: insertion to the right of the
32 fixed labels in the independently verified one-point-extension experiment.
The input is the original, unchanged 5,456-variable / 69,408-clause DIMACS:
SHA-256 `b55d1e4fb876ab89cf9f86581db2da948564996e320193c70493fbd4d4b8912a`.

`Slot32Containment.lean` constructs Lean formula definitions and three
closed kernel theorems:

- `slot32ContainsCore` proves that every core clause belongs to the full
  numbered formula. In Mathlib's direction convention, the full
  formula **subsumes** the core.
- `slot32FullUnsat` proves the empty clause from the full numbered formula.
- `slot32NoAssignment` states that no valuation satisfies that formula.

The command uses Mathlib's DIMACS parser **at elaboration time** with a
check for end-of-input and the expected dimensions. It builds a balanced,
chunked expression of the full list of all original clauses. For each
core clause it finds an exact ordered-literal match with the original
IDs and reconstructs a path from that clause into the full list.
The Lean kernel checks the formal inclusion proof and the derived
UNSAT theorem. The parser itself is not proven correct in Lean,
and the theorems are about the instantiated Lean formula definitions,
not a formal predicate linking those definitions to the file bytes.
The published SHA-256 explicitly identifies the inputs.

DRAT-trim's initial core extraction can reorder the literal list within a
clause. `restore_literal_order.py` chooses the exact original ordering for
the 60 extracted clauses, with all original variable numbers unchanged.
Plain Kissat solved this reordered core afresh, then DRAT-trim in RUP-only
mode emitted the included LRAT against that exact reordered file.
The kernel verifies this fresh core proof and exact ordered-clause
containment, so it does not assume either the solver or the extractor is sound.
The only axiom reported on all three statements is `propext`.
No `native_decide` axiom or `sorry` is used.

## Replay

Generate the exact full instance from the published extension bundle:

```sh
python3 extension32.py ./generated
```

With Lean 4.36.0 and Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` built, run from that Lean project:

```sh
bash /path/to/numbered-pilot/verify.sh /path/to/generated/slot-32.cnf
```

An executable `LEAN` plus configured `LEAN_PATH` can stand in for
`lake env lean`. This replay checks all three file hashes and needs
neither Kissat nor DRAT-trim. To reproduce the core and conversion instead:

```sh
python3 restore_literal_order.py original.cnf extracted_core.cnf core.cnf
kissat --plain core.cnf core.drat   # exit 20 means UNSAT
drat-trim core.cnf core.drat -U -L core.lrat -q
```

Used [Kissat 4.0.4](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.4)
and [DRAT-trim 2e3b2dc0](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985).

## Scope and next link

[Damásdi, Dong, Scheucher, and Zeng, *Saturation results around the
Erdős–Szekeres problem*](https://doi.org/10.1016/j.ejc.2025.104236)
already proved that the original Erdős–Szekeres cup–cap construction is
saturated. The present exact sign-pattern experiment and Lean kernel
certificate are a computational and verification reproduction in that
context, not a new standalone saturation result.

The other 32 slots have kernel proofs of their extracted cores and
independently checked containment; they were not replayed with this
numbered-formula Lean containment method. To adapt this pilot, pass the
original slot and its extracted core through the literal-order restorer,
re-solve that exact core in plain RUP mode, and set the expected core
clause count in the command. Use few concurrent runs: constructing
the complete formula for each slot takes memory, and the pilot's
compiled object was about 25 MB.

The specialization from abstract geometric clauses to these exact
numbered DIMACS IDs is not yet formalized. It requires a formal link
between the lexicographic pair/triple numbering, fixed old-only
orientation constants, and clauses selected for old convex six-sets.
Only the clauses used in a certified core need such a justification
for a direct geometry-to-core proof. This is not a complete Lean
proof of the extension experiment or a result for arbitrary 33 points.
