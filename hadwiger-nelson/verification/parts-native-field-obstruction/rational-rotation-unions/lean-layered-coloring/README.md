# Lean-checked abstract layer-and-block five-coloring

`LayeredFive.lean` is checked in Lean **4.36.0**, commit
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, with `import Init`
only and warnings treated as errors. It has no `sorry`,
project axioms or native proof calls.

The precise checked existence theorem is
`LayeredFive.Scheme.exists_proper_five`:

    ∃ c : V → Fin 5, ∀ {x y}, G.edge x y → c x ≠ c y

under the hypotheses of the abstract structure `Scheme`.
`#print axioms` reports exactly `[propext, Quot.sound]` for
this theorem. The separate `proper` declaration asserts
properness of the explicit map `G.color`.

The input is an abstract symmetric edge relation on a type of
vertices. Level zero comes with proper colors. Every positive
block has four residue labels and at most one target vertex
at a strictly smaller Nat level. When an edge runs to a lower
level, its endpoint agrees with that target in either:
(1) level zero and base color, or (2) positive level, block
and residue. Inside each positive level, only vertices of
one block with distinct residues can be adjacent. These
conditions are stated entirely before the color recursion.

The construction uses `WellFounded.fix` with the inverse image
of Nat's strict order. Color a positive vertex by injecting
its four residue values into five colors with one value
forbidden, namely the color of its block's unique lower target.
A block without target drops color 4.

Intended arithmetic interpretation, **not formalized here**:
for the two-copy Parts theorem, use level zero for integral
vertices, positive level `-v(x)` for the others, and block ID
(side, additive coset mod O). The residue is mod 2O within
that coset. The deterministic local approximation in the
[full-field proof](../hn-parts-full-field-gluing/README.md)
picks one representative matching all actual lower endpoints
in color data. Neither the field construction, the valuations,
the cross-edge incidence results, nor the concrete arithmetic
instantiation is included in this Lean proof.

## Replay

From this directory, either run Lean 4.36.0 directly:

```sh
lean --threads=1 LayeredFive.lean
```

or reproduce the attached Linux x86-64 pinned run:

```sh
sha256sum -c SHA256SUMS
timeout 22s python3 guarded_replay.py PATH_TO_LEAN_4_36_0
```

The guarded checker tests the executable SHA-256 and version,
clears any inherited Lean import path, uses a local temporary
directory, one Lean worker, Lean's 1,000 MB internal memory
limit and a sampled RSS guard of 1,500,000 KiB. The successful
replay exited 0 after 0.605 s at sampled peak 479,092 KiB.
`replay.log` records the exact output; rerunning the wrapper
updates that log.
