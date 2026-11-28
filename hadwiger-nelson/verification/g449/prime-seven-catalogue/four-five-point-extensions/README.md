# Four arbitrary points, and five points with at least one off-grid

**Result.** Every induced extension of the fixed G449 by at most four points
anywhere in the plane is five-colorable. An extension by five distinct new
points is five-colorable if at least one lies outside the denominator-seven
cyclotomic grid. An extension by five **grid** points is
not covered. This does not change the known 6–7 bounds for the whole plane.

[Aafi Khan Malek's paper (PDF)](paper/four-point-extensions.pdf) · [TeX](paper/four-point-extensions.tex)

## Replay from a clean checkout

Use Python 3.10+ with NumPy and a C++20 compiler. Obtain `G449.k21` and
`G449.s6` from the [original authors' pinned commit](https://github.com/bprzybocki/G449/tree/125bfda97ed1d336f84694de04dedcfb349c5164).
The checker pins and verifies their SHA-256 hashes. From this directory:

```sh
sha256sum --strict -c SHA256SUMS
bash replay.sh PATH_TO_PINNED_G449_INPUTS
```

The parent directory contains the preceding
[three-point theorem and its replay](../three-point-extension.md), the exact
[direction catalogue](../README.md), and the needed bank of 36 base
colorings. To replay more generally, set `G449_CATALOGUE_DIR` to that directory
and `CXX` to a C++20 compiler if not `g++`. Run without Python's `-O`
or C++'s `NDEBUG`, since assertions are part of the checker. No SAT solver
or floating-point tests are used in the replay. These are exact code
checks plus the written proof, not Lean verification.

The program builds the full 7,056-candidate grid graph from the verified
directions, enumerates the five connected-component partitions of four
new vertices with sufficient total degree, and independently checks the
five-coloring of the 735-vertex union of all 8,629 residual quartets.
A separate spanning-star and path enumerator and nonedge-pair joins agree
row for row on the residual quartets. The independent Laurent-polynomial audit
recomputes all 269,745 pairwise
distances on that union. Two further modular replays enumerate the full
mixed-triple universes in the proof, and triples containing a unit edge
are removed where appropriate by the geometric observation in the paper.
Every
surviving mixed triple has an exact grid circumcenter.
