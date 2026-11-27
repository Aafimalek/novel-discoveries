# All-low-pairs-used geometry in Lean

In a linear size-17 design with minimum degree two, suppose every pair
of degree-two labels from different coordinates is used. Lean proves
there is one such label in each coordinate, all other labels have
degree three, the four low labels form a placed word, and they have
four distinct additional incident words, each with just its own low.

The key lemma is that four distinct pairwise-intersecting two-element
sets have a common member: if three form a triangle, any two-element
set intersecting all three is already one of the triangle edges.
Apply this to the four incident-word sets. To prove uniqueness of
the low label in a coordinate, replace it by a second candidate: both
resulting words would have the same remaining three coordinates,
contradicting linearity unless they are equal.

Build `EulerAllUsed`, `EulerAllUsedProfile`, then
`EulerAllUsedFrequencies` with `LatinGap` and pinned Mathlib on
LEAN_PATH. The included logs report only the three standard axioms.

The four outside words have not yet been formally normalized to the 17
archived diagrams, and the free-label symmetry cuts remain separate.
