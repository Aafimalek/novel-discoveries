# Any five added points preserve five-colorability of G449

**Theorem.** For any set of at most five points in the Euclidean plane, the
induced unit-distance graph on their union with the fixed 449 vertices
of G449 is five-colorable. A six-chromatic extension of this specific
point set would need at least six new points. This does not change the
known 6–7 bounds for the whole plane.

[Aafi Khan Malek's paper (PDF)](paper/five-point-extensions.pdf) · [TeX](paper/five-point-extensions.tex)

The previous [exact computation and proof](../four-five-point-extensions/)
handles up to four arbitrary points and any five with a point outside the
denominator-seven cyclotomic grid. To finish, assume five distinct new grid
points; a new point of total degree at most four can be colored last.

* The remaining degree-one case has a single new hub adjacent to all four
  others. Enumerating every possible hub and four eligible rim points gives
  872,165 candidates, of which 6,839 pass the degree test. The 18 checked
  base colorings cover all of them; the replay also tests the list solver
  against direct assignment enumeration.
* For all new points of base degree at least two, the candidate graph has
  7,056 vertices and 33,908 exact unit edges. Enumerate degree-admissible
  connected components and group them by the set of base colorings that
  support their list coloring. Expand only compatible choices of components
  that have no shared supporting base coloring. The resulting 138,009
  unresolved configurations are covered by a single stored coloring of their
  union (797 vertices and 4,532 edges). An independent enumerator agrees on
  every residual set, and a separate Laurent-norm audit recomputes all
  317,206 distances in the witness union.

## Replay

Obtain `G449.k21` and `G449.s6` from the [original authors' pinned commit](https://github.com/bprzybocki/G449/tree/125bfda97ed1d336f84694de04dedcfb349c5164).
With Python 3.10+, NumPy and a C++20 compiler, run:

```sh
sha256sum --strict -c SHA256SUMS
bash replay.sh PATH_TO_PINNED_G449_INPUTS
```

The parent directory supplies shared input and arithmetic helpers; its
`four-five-point-extensions` subdirectory supplies the earlier witness and
candidate generator. Optionally set `G449_CATALOGUE_DIR` and `G449_FOUR_DIR`
to those directories explicitly. The replay regenerates the exact search,
requires input and residual hashes, and checks the supplied coloring.
It uses no SAT solver, floating-point tests, or Lean statements.
The theorem combines this replay with the earlier published four-point and
mixed-five-point proof.
