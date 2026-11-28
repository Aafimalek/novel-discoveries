# C14 sorted trace: entire static scan and indexed replay design

This is not a Lean checking result. The previously published two-slice pilot
checked three exact additions only. No Lean was invoked for this milestone.

Inputs: the selected sorted `alternatives/14/1.cnf` and `1.lrat`, identified
by full SHA-256s in `out/summary.json`. Reproduce with Python 3 under a
350,000 KiB address-space limit and an 85-second timeout; from this directory:

```sh
(ulimit -v 350000; timeout 85 python3 analyze.py PATH/1.cnf PATH/1.lrat out)
```

All 5,085 additions are in the exact terminal-empty dependency graph. The
8,825 original rows include 8,267 in the graph. There are 816,462 hint
references. The Python checker compares exact ordered clause literals and
one-based IDs, respects every archived deletion, rejects nonpositive hints,
checks each unit propagation and requires the last hint be a conflict for
each addition. This identifies the exact terminal empty at original ID
17658. All raw trace lines were read; bytes and hashes cover the actual
selected files, not the larger unsorted alternatives.

The report and deterministic gzip files in `out/` describe exact pre/post
sets at every planned cut (recorded as ID lists); the lookup mapping is in
`exact-cone.json.gz`. A retained ID at cut k (just before learned ordinal
k) has definition before k and last reference at or after k. Terminal
empty has one virtual use past the final addition. Local imports are
precisely earlier IDs directly used in the chunk; carried rows without
immediate use are not local imports. External membership assertions are
audit only. Chunk byte intervals slice the exact archived file, possibly
containing deletion rows between their additions.

| Additions/chunk | Chunks | Largest pre-frontier | Largest local imports | Max hint work per chunk |
|---:|---:|---:|---:|---:|
| 24 | 212 | 8,267 | 1,844 | 8,984 |
| 64 | 80 | 8,267 | 2,427 | 19,607 |
| 128 | 40 | 8,267 | 2,977 | 33,506 |
| 256 | 20 | 8,267 | 3,725 | 63,046 |
| 512 | 10 | 8,267 | 4,439 | 114,289 |

Do **not** scale the pilot by enumerating 6,000–8,000-row frontiers
in every theorem type, or by constructing 816,462 linear `List.mem`
chains. The case is pure RUP, so using an already established clause
logically after a deletion would be sound (even though this exact trace
does not). Thus the Lean proof needs a *monotone* dense prefix:

1. Define transparent exact row data with stable dense positions. Original
   positions are 0–8824; learned positions are 8825–13909. Reindex each raw
   hint once to a previous slot, and preserve ID→slot diagnostics. Use a
   balanced directory of named data blocks and e.g. local proof-side row
   aliases; a closed lookup should unfold at most a directory path and
   one short leaf. Initial experiment should measure this, rather than
   assuming kernel arrays or opaque recursion reduce efficiently.
2. Prove a single indexed initial-rows bridge for the original formula.
   Use a balanced array/tree and an aligned-value relation (or one
   generic list-indexing lemma with a definitionally aligned array);
   it must not rely on hashes or trust the Python projection.
3. For each addition with slot j, generate a theorem from
   `GoodBelow base rowAt j`: each hint has kernel-checked `k < j` and
   an *exact* typed lookup `base.proof (rowAt k)`. The metaprogram can
   instantiate Mathlib's existing `buildProofStep` on those proof
   terms against the common original base and validate by ordinary
   kernel conversion to the explicit clause. It need not build an
   explicit local formula whose membership is later re-proved.
   If casts on repeated hints are expensive, put exact lookup equalities
   behind named theorems, amortized once per slot.
4. Within a chunk extend prefix knowledge by one slot at a time using the
   draft interface. Expose only one small `Slice base rowAt lo hi`
   theorem. Compose in a balanced DAG if linear importing is expensive;
   chunk headers import generic data plus earlier **data** as needed,
   never earlier proof modules. The top-level composer imports the
   slice theorems. It applies the checked initial prefix and extracts
   the empty at dense slot 13909.
5. The input archive-containment/geometry theorem stays separate.
   Result claims must distinguish raw static trace validity, kernel
   verification of C14 core unsatisfiability, and composition with the
   archived branch's geometric formula.

`EulerC14IndexedDraft.lean` is a small deliberately uncompiled interface
for steps 2–4. The two harder implementation risks are efficient kernel
lookup at a closed concrete clause and proof-term size for rows with up
to 849 hints/108 literals. The next authorized Lean measurement should
benchmark separately one early chunk and one worst-work single row
(`frontiers-24.json.gz` plus `exact-cone.json.gz` identify them).
An alternative internal evaluator would prove soundness of a Boolean
single-step RUP function over exact row arrays, then use ordinary
kernel certificate reduction per tiny block; avoid `native_decide`
if the deliverable is intended to match the existing axiom audit.
