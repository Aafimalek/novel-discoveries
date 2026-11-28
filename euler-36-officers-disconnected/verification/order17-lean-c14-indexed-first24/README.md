# Indexed C14 pilot, first 24 learned additions only

Verified with ordinary Lean 4.36, warning-as-error, single worker.
The source starts from the previous static design; the checked artifacts
and axiom log supersede that draft status banner.

`Euler.C14.IndexedDraft.first24 : Slice base rowAt 135 159` covers the
first 24 additions, raw sorted C14 IDs 10716–10739, and all of their 263
positive hint references. The first 135 slots are the originally numbered
rows directly referenced, in sorted ID order, packed locally; slots
135–158 are the exact learned clauses in order. All lookups are indexed:
per hint the kernel checks a closed comparison and that the exact slot's
clause is definitionally the clause in the generated proof. There are no
per-hint list membership proofs. The Mathlib RUP term producer emits
ordinary kernel theorems; its metaprogram uses eval only to extract inputs.
`Euler.C14.IndexedDraft.local_cnf_alignment` is axiom-free, and
`Euler.C14.IndexedDraft.first24_fromExactLocalCNF : GoodBelow base rowAt 159`
needs no prefix assumption and uses only `propext`.
The pilot does not assert anything about the rest of the trace.

The concrete base is the explicit 135-row local CNF, **not** the 8,825-row
archived original. Linking the exact selected rows to the archived original
CNF inside Lean, the full proof through the empty clause, and the geometry
composition are outside this pilot. Sparse raw IDs are externally audited
in the earlier `euler-c14-whole-trace-static` package; their theorem-facing
interpretation is exact signed literals at stable local slots, not raw IDs.

Set LEAN_BIN and LEAN_MATHLIB_PATH as described in replay.sh, then run
`./replay.sh`. The source `gen.py` optionally regenerates the large pilot
from the static package's exact cone. Proof builds do not need that package.
