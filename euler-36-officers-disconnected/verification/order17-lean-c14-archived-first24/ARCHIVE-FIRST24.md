# C14: first 24 learned clauses directly from the archived sorted core

The input is the archived sorted DIMACS core (the included exact
`c14-sorted-core.cnf`, 149167 bytes; copied from alternatives/14/1.cnf,
not the larger unsorted alternative). The Lean metaprogram parses it
with mathlib's DIMACS parser, rejects an unparsed suffix, checks
dimension 10646 variables and 8825 rows, and builds a balanced typed
formula from every literal in order. It generates a kernel proof of
membership for all 135 selected exact clauses, at their one-based
DIMACS row IDs; the combined declaration's type refers to the existing
explicit local CNF from the first24 indexed pilot. SHA-256 identifies
replay bytes, never stands in for a Lean membership proof.

The checked top theorem is
`Euler.C14.IndexedDraft.first24_fromExactArchivedCNF`:
`GoodBelow archivedSortedCore rowAt 159`. This means the 8,825-clause
sorted archived core entails every local slot of the initial indexed
pilot through its 24th learned addition (raw ID 10739 inclusive).
Both the bridge and the following finite subformula inclusion use only `propext`.
`Euler.C14.IndexedDraft.archive_subsumes_exact_local`:
`archivedSortedCore.subsumes base`.

Run `./replay-archive.sh` using the pinned Lean 4.36 and mathlib
directories; it builds the generic interface, driver, explicit pilot,
initialization, archived parser/subsumption driver, and final bridge in
ordinary warning-as-error Lean. See separate audit logs for verification.

This is not C14 unsatisfiability, later learned rows, terminal empty,
or a checked relation between the sorted core and the entire pre-core
geometric branching formula.
