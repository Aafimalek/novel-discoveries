# Lean-checked C10 frontier interface and first RUP addition

Both Lean modules and a separate axiom audit passed with Lean 4.36.0
and pinned Mathlib, ordinary kernel, one worker, 2,300 MB configured limit.
The independent Python prefix check also executed successfully. This is
not a checked C10 core refutation and does not address the separate
degree-one geometry-to-formula gap.

## Typed frontier

`EulerRupFrontier.lean` defines a frontier as ordered pairs of an exact
natural clause ID and a `Sat.Clause` (ordered literal list). A slice is
`Transformer inputs outputs`: each exact output clause is proved from
the small formula of its exact input clauses. It does not mention the
original CNF or import any previous slice. `apply_transformer`
lifts the whole slice to any common base formula given proofs of the
named input rows, and `transformer_comp` composes boundaries.
Proof of a row in the live-in frontier requires the specific exact pair,
not a matching ID or hash alone. Row IDs are trace bookkeeping, not
propositions whose truth can replace clause proof. Duplicate/fresh IDs
and deletion liveness should also be validated by any archive driver;
sound logical implication itself needs no uniqueness assumption.

## Actual C10 first addition

The checked small raw prefix starts after the opening deletion row at
ID 14664. Its first addition 15051 has positive RUP hints 12732, 50,
12733. All are live original core rows. The ordered original signed
clauses are [1], [-1,1297], and
[-1297,1298,1299,1300,1301,1302,-9721]. Falsifying every literal of
the target [1298,1299,1300,1301,1302,-9721] propagates 1 and 1297,
then conflicts on row 12733. The checked Lean theorem implements this by
two nested negated implications, without excluded-middle steps. It
exports the corresponding one-output transformer and a statement
applying its three typed assumptions to an arbitrary original context.

Reproduce the ordinary Python analysis without reading the rest of the
74 MiB trace:

```sh
python3 check_first_prefix.py PATH_TO_ARCHIVED_CASE_10
```

The script reads two LRAT rows and at most 12,733 (small) core CNF
rows. It does not perform a solver call, parse the full LRAT, or prove
anything about the 40,991 later additions. Full input archive hashes
remain in the existing C10 blocker report. For Lean replay, put pinned Mathlib and upstream packages' compiled
library directories plus this directory on `LEAN_PATH`. Run:

```sh
lean -j1 -M2300 -o EulerRupFrontier.olean EulerRupFrontier.lean
lean -j1 -M2300 -o EulerC10FirstRow.olean EulerC10FirstRow.lean
lean -j1 -M2300 AuditFrontier.lean
```

The local first-row implication is axiom-free, the typed slice uses
`propext`, and its transfer to a common base uses `propext, Quot.sound`.
The generic composition audit shows the same standard axioms only.
No admitted, native-evaluation, or project-specific axioms were used.

## Next bounded implementation steps

1. Define an independent bounded slice importer: stream selected LRAT
   lines/metadata with checked initial live IDs, no negative/RAT hints,
   and exact ordered literals. Collect exact live-in rows first read
   before being produced within a slice. Define its small formula
   as `frontierFormula inputs`. Compiled initial rows use membership
   in this small formula, never prior slice imports.
2. Adapt the existing `FactoredDriver`: reuse
   `Mathlib.Tactic.Sat.buildClause` and `buildProofStep` under that
   small context. Accept nonempty ending rows and export the subset
   needed by later slices. Do not compile one module containing
   all 40k additions, and do not close a slice with a declaration
   that assumes a numeric ID is automatically proved.
3. In exact archive assembly, establish original core membership
   of initial live-in rows, check (or derive) each boundary in
   dependency order, and use `original_refuted_of_empty` only after
   deriving the actual terminal empty row. Parallel-independent
   slice compilation reduces per-file parser/elaborator state;
   the final transitive import working set and axiom audit must
   still be measured. Carry or re-supply an unmodified predecessor
   row when later slices use it; no stage may invent a clause.
4. C10 remains the degree-one anchor-max-5 case. Neither this prefix
   nor a completed core refutation establishes its exact degree-one
   geometry model or a geometric exclusion.
