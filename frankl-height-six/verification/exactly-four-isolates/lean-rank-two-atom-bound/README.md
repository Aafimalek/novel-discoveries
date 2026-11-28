# Verified rank-two atom counting and saturation

The three sources compiled on pinned Lean 4.36 / Mathlib with one
worker, a 2500 MB cap and workspace-overlay TMPDIR. All three
compilations exited zero without warnings. The sixteen public
axiom audits list only propext, Classical.choice and Quot.sound.
The successful replay is replay.log; failed attempts are not audited.

For a finite intersection-closed family D supported in U, containing
the empty set and no strict four-member chain, let a be its number
of nonempty inclusion-minimal members (atoms). The exact checked
endpoints are:

- FranklRankTwoAtoms.card_le_support_add_choose_atoms:
  |D| <= 1+|U|+binom(a,2).
- FranklRankTwoAtoms.singleton_atoms_of_large_card:
  if 1+|U|+binom(|U|-1,2) < |D|, the atoms are precisely the
  singleton subsets of U.
- FranklRankTwoAtoms.pair_mem_of_quadratic_card_eq:
  if every singleton subset of U is in D and the size is
  1+|U|+binom(|U|,2), every two-point subset of U is in D.

The count injects nonatoms with at least two atoms into pairs of
atoms, and the other nonatoms into points covered by no atom.
Pair saturation uses an injection avoiding any alleged missing
pair and contradicts equality.

The only project-specific foundation import is FranklHeightThreeSauer
(for the existing no-four-chain predicate); the claims themselves
are generic finite set-system theorems. This module does not yet
identify complemented compressed Frankl pair fibers with these
hypotheses, produce mixed witnesses, check the multi-source exactly-four
endpoint, or prove the entire at-least-five bound.

Replay from source with Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` on `LEAN_PATH`.
Use `bash replay.sh`; it first builds the included Sauer module
and then replays the three new modules serially.
