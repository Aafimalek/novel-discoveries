# Checked reusable production orientation rank

`OrientationRank.lean` passed strict pinned Lean 4.36.0. It imports
only the already verified actual `EndpointConcreteSpec` and Lean core.
Its checked theorem is

    production_sign_id (hab : a<b) (hbc : b<c) :
      (dictionary n A B).idxOf (.sign a b c) + 1 = rank a b c

for arbitrary `n A B : Nat` and `a b c : Fin n`. The result depends
neither on the cap/cup sizes nor on precomputed facts for a 32-label
sign table. The 1-based rank formula in usual notation is

    1 + sum_{i<a} sum_{i<j<n} (n-j-1)
      + sum_{a<j<b} (n-j-1)
      + (c-b-1).

The inner first-block sum is exactly C(n-i-1,2). The Lean definition
keeps the same count as a sum of numeric suffix lengths rather than
introducing a Mathlib dependency for binomial coefficients. No
compiler dictionary, triple list, formula clauses, or side-cell
table needs to be scanned to evaluate this arithmetic rank. First
and second block prefix sums can be reused across many literals;
the suite does not yet prove a separate binomial closed-form theorem.

## Proof structure

1. Split the actual `List.finRange` at a typed label using its
   `take` and `drop` at the exact index. Membership in the
   before/after parts implies strict inequality, by indexed list
   membership and `getElem_finRange`.
2. Filtering the range for labels larger than a fixed label yields
   precisely its suffix. Filtering the prefix before c for labels
   larger than b has length c−(b+1), because the prefix decomposes at
   b+1 into a discarded initial segment and retained suffix fragment.
3. Reassociate the actual two production `flatMap`s as
   first-label then second-label blocks. Last blocks contain only
   actual `.sign a b c` constructors with ordered c; their lengths
   are n−(b+1). First-block lengths are the sum of those suffix
   lengths. Constructor injectivity excludes any earlier block from
   containing the target.
4. Apply the generic `idxOf` concatenation lemma twice, and at the
   end show that the initial sign table, not either side table,
   contains the key. This establishes exact production rank despite
   not needing disjointness or uniqueness of the cap/cup dictionaries.

The standalone arithmetic test `python3 replay_rank.py` checks the same
expression against independent lexicographic combinations for every one
of 40,920 triples over n=3..32. That test is not used as a proof
hypothesis or a substitute for the strict Lean proof.

## Strict replay

Use pinned Lean 4.36.0, warnings as errors, one worker, overlay TMPDIR,
and the existing `EndpointConcreteSpec`, `NumberedCNF`,
`EndpointBaseAliases`, and `EndpointGuardCore` objects and receipts.
In a new overlay containing `out/` and `tmp/` run
`python3 run_stage.py OrientationRank 84`. The runner checks the pinned
executable and exact prerequisite objects and records Lean's printed
axioms, timing, sampled and reported RSS, and source/object/log digests.
This module does not prove contiguous offsets of external text,
checker equality, any larger packet chunk, or target UNSAT.
