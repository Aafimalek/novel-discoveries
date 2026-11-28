# Checked C14 exact original archive prefix and first 72 learned rows

This supersedes the static scope header in README.md. The proof is built
with ordinary pinned Lean 4.36, one worker, memory cap 2450 MB, strict
warnings. The dependency is the checked first48 global index source
package SHA fa85e3a37ddd08a3697f956b58f11d7b712220357e7881d8b6544dfe39c4ad3e.
Use its build first, then replay-checked.sh with the three environment
variables shown. Fresh build objects are local only.

The exact sorted original DIMACS (8,825 clauses, 10,646 variables) is
included. The Lean command parses it and constructs a formula with the
original row order and exact clause literals; it uses no hash proof, no
unproved sorted membership, and no file outside the package at replay.
The original 69 block equalities, one partial last block of 121 rows
included, relate that archive to the exact permanent rowAt. The old
separately checked 135-row local first24 proof and its differently
parenthesized archivedSortedCore type are not imported for any theorem
in this replay.

Theorem audit (Euler.C14.Production namespace):
* exactSortedArchiveInitial : GoodBelow archivedGlobalCore rowAt 8825.
* first48_fromExactGlobalArchive : GoodBelow archivedGlobalCore rowAt 8873.
* first72_fromExactGlobalArchive : GoodBelow archivedGlobalCore rowAt 8897.
  These three report propext, Classical.choice, Quot.sound.
* chunk_8873_8897 and chunk_9254_9278 are conditional typed slices sharing
  the identical rowAt constant, and report propext. The first advances
  the exact contiguous baseline by 24 learned additions (481 hints),
  ending at raw ID10788. The second is separate; it shows the driver
  handles actual learned dependencies across slices, with 43 earlier
  learned IDs and 376 hints. It does not cover gaps between intervals.

Full LRAT through terminal empty, full-formula core containment and
geometry not reached. Source files are historically named Draft;
per-module strict logs and receipt hashes show the verification result.
