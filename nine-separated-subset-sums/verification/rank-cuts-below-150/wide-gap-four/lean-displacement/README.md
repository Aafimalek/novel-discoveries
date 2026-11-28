# Lean checks for the wide-branch displacement argument

Pinned Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` checked two theorems:

- `exact_gap_displacement`: two ordered signed ranks with monotone
  errors in an interval of width below two have the prescribed
  integer displacement when their value difference is in the
  corresponding half-open band. This is a real arithmetic lemma.
- `wide_three_top_collision`: the four abstract signed-rank inputs
  at indices 49, 56, and 63 are mutually inconsistent, as used in
  the written exclusion of normalized gaps in `[3,4)`.

The first theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`; the second depends only on `propext`. No native
computation or additional axioms were used. The surrounding
subset-sum identities and geometry establishing these hypotheses
have not been checked here, and this does not formalize the whole
written wide-gap-four theorem or improve the bound 149.

With the pinned Mathlib on `LEAN_PATH`, replay with
`lean -j1 -M2300 WideLiftRanks.lean` and compare the axiom audit.
