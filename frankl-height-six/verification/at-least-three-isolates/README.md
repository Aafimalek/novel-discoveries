# At least three isolates: end-to-end Lean proof

**Verified theorem:** `FranklForcingFiber.three_le_isolated_of_weakMinimalGround`.
In the height-six model, the proper forcing graph of a minimum-ground weak
family must have at least three isolated points. The family is finite,
nonempty, union-closed, contains no empty member or seven-member
strict chain, and every point occurs in at most half its members.

[Paper PDF](paper/few-isolates.pdf) · [TeX](paper/few-isolates.tex) ·
[Checked Lean proof](lean/FranklAtLeastThreeIsolates.lean)

A clean compilation of the new source against the previously built
Lean foundations verified the entire theorem, including the zero- and
one-center branches and the two-or-more-center counting argument.
The proof and its two main lemmas use only `propext`, `Classical.choice`
and `Quot.sound`, as recorded in [the axiom audit](lean/rebuild.log).
No external verification step or finite search is an assumption
of the theorem.

Use Lean 4.36.0 and Mathlib revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Put the built
[Lean foundations](../../lean/) and
[signature-Sauer modules](../signature-moments/) on `LEAN_PATH`, then run:

```sh
lean -j1 -M2350 lean/FranklAtLeastThreeIsolates.lean
```

The stronger [four-isolate lower bound](../at-least-four-isolates/)
is a written proof with Lean-checked ingredients, not yet a full Lean
theorem. Frankl at height six remains open.
