# A kernel-checked core from one size-17 Euler branch

This is a pilot for one case, `aus-0111_1012_1203_1320`. The archived
60,567-clause input has SHA-256
`00b1bf0edffac4f5008c82475f22dff03a89dae040be0b268f2d6f28a63cea38`.
The proof derived here is against a **2,646-clause extracted core**,
not directly against the complete input.

## Extract a core and generate pure RUP evidence

With the exact archived files named `original.cnf` and `native.drat`,
use Kissat 4.0.4 and DRAT-trim at
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`:

```sh
drat-trim original.cnf native.drat -c first.cnf -q
kissat --plain first.cnf first.drat  # UNSAT is exit 20
drat-trim first.cnf first.drat -U -c core.cnf -q
kissat --plain core.cnf core.drat     # UNSAT is exit 20
drat-trim core.cnf core.drat -U -L core.lrat -q
python audit_containment.py original.cnf first.cnf core.cnf
sha256sum -c SHA256SUMS
```

The archive includes the final `core.cnf` and its `core.lrat` so
kernel replay does not require the solver or the full original.
For external containment against the final core alone, run
`python audit_containment.py /path/to/original.cnf core.cnf`.
`UPSTREAM-SHA256SUMS` records the unbundled original/DRAT and
intermediate artefacts if regenerating.

The first pass leaves 3,156 original clauses, the second 2,646.
The final LRAT is 169 KiB, with 185 learned core steps including
the empty clause, 32,495 resolution steps, and no RAT steps. The
variables retain their original numbers. DRAT-trim can reorder
literals within a clause, so the separate Python containment audit
compares multisets of clauses with sorted signed literals; it is
not a theorem in Lean.

## Kernel replay

With Lean 4.36.0 and the project's Mathlib on the module path:

```sh
lean -o FactoredCore.olean "$PWD/FactoredCore.lean"
```

The Lean elaborator uses `Mathlib.Tactic.Sat.buildProofStep` to
build an explicit proof for each learned clause, adds an opaque
kernel-checked theorem for that step, and refers to it by name.
This avoids the excessive memory of one monolithic proof term
and avoids reification into one proposition with thousands of
binders. The final theorem `allused_core_unsat_factored` proves
the empty clause from its internal parsed core formula. The build
took about 19 seconds at a 1.8-GB Lean cap, and
`#print axioms allused_core_unsat_factored` prints only
`[propext]`. There is no `native_decide` or admitted proof.

The kernel theorem does not formalize extraction, byte parsing,
containment in the full original DIMACS, its geometry, or any
other branch of the Euler proof.
