# Checked ES33 real geometric reflection and lex witness choice

These two files passed against the rebuilt ES33 Prelude/Anchor stack,
with exact previously audited real determinant and abstract lex objects.
The only elaboration adjustment to the staged source is one additional
unfolding in the proof of mirror_twice; see georef-elaboration.diff. No
theorem statement or hypothesis changed.

Lean 4.36.0, Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
One worker, warning-as-error. GeometricReflection: 9.070 s,
2,029,984 KiB peak child RSS; GeometricReflectionLeader: 43.607 s,
1,590,920 KiB peak child RSS. All seven emitted theorem audit lines
are exactly the core propext, Classical.choice, Quot.sound set.

Scope of the checked theorems:

- For any indexed real plane embedding p, negating the x
  coordinate and reversing labels gives orientation signs
  χ'(a,b,c) = χ(rev c, rev b, rev a), without sign complementation.
  Strict increasing x-order and ordered general position transfer.
- For an embedding with ordered general position, absence of a
  seven-point subset in ConvexPosition survives reflection. The proof
  uses the previously checked odd-quartet criterion, transports the
  finite index set along label reversal, and preserves XOR parity.
- The abstract Residual32 predicate transfers on the actual reflected
  embedding, including its exact “no positive six-set” condition.
  Each positive set would map back to an equally large set with the
  same positive ordered triple signs.
- For any fixed list of triple orbit representatives, the pair word
  of the reflected embedding is the original pair word with each
  pair swapped. Hence real_lex_representative proves existence of a
  RealWitness with a true guarded lex leader iff some RealWitness
  exists. A RealWitness is an actual 32-point plane embedding with
  increasing x-order, ordered general position, and Residual32 signs.

This theorem concerns a supplied orbit list, not a Lean validation of
the 2,480 concrete pairs or their numerical variable IDs. Neither
actual DIMACS containment, text serialization, solver certificates,
nor target UNSAT is claimed. The separate interface between the real
33-point normalization and extraction of a RealWitness is not added
here. Reuse only the fully rebuilt matching Prelude/Anchor objects,
not any unrefactored legacy build root.

The archive includes all sixteen local source modules needed
to rebuild the checked stages, in `rebuild.sh` order. Extract
into a new directory and use pinned compiled Mathlib and only
its package libraries on `LEAN_PATH` (no old ES33 objects).
The source comment in GeometricReflection.lean retains the
original draft label for byte reproduction; the accompanying
current compiler receipts verify the file. The audited run
built the components over successive fresh-stack waves, not a
separate all-in-one run of the release script.
