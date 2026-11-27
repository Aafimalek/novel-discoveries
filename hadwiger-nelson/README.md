# Hadwiger–Nelson: exact coordinate and finite-field experiments

The published unrestricted bounds remain 6 and 7. OpenAI's [preprint](https://github.com/openai/math/blob/main/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf) proves the lower bound for arbitrary colorings, while its [formalization note](https://github.com/openai/math/blob/main/lean/docs/158.md) points to both bound proofs. None of the work here improves those bounds.

## Lean witness interface

- `AlgebraicWitness.lean`: coefficientwise exact rational edge verification in EuclideanSpace ℝ (Fin 2) and transfer of a finite k-coloring obstruction to the unrestricted plane.
- `MoserWitness.lean`: textbook seven-vertex Moser spindle as a smoke test. Checks all eleven edges and formally rules out three colors.
- `ExactEdges.lean`: proves independence of the four radicals under rational nonsquare hypotheses, so the exact test is complete as well as sound. Also connects a finite refutation to the actual Mathlib chromatic number of the whole Euclidean plane; use k=6 for a potential resolution of the unrestricted problem.
- `ModFive.lean`: an explicit proper five-coloring for arbitrary fixed denominators prime to 5, in independently generated biquadratic coefficient lattices whose integral radicands reduce to 3 and 1 mod 5. The special case (3,11) does not improve the prior full-field result: Fischer proved that this plane has chromatic number four; see the [modern formalization and attribution](https://github.com/decalion89/chromatic-number-of-the-plane). The finite arithmetic table is evaluated by the Lean kernel (`decide +kernel`), not a compiled decision axiom.

All four Lean files were built with official Lean 4.36.0 and Mathlib. The displayed theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Finite quotient

Consider the field F25 = F5[T]/(T²−3) and its graph on F25² with edges (x−x′)²+(y−y′)²=1. The projection (a+bT,c+dT) ↦ a+c+2d assigns five colors and is proper by the table in `ModFive.lean` with t=1.

The following separate exact proof shows this finite quotient requires all five colors, and does **not** imply a lower bound of five for any real lattice. The additive group is F5^4 and the graph is Cayley with 24 generators, the unit directions. The 625 Fourier characters indexed by a∈F5^4 form an orthogonal eigenbasis. The eigenvalue of character a is n0 + n1(ζ+ζ⁻¹) + n2(ζ²+ζ⁻²), where ζ is a primitive fifth root and n_j counts the unit directions whose dot product with a is j mod 5. Each direction's negative is also a direction, so n1=n4 and n2=n3. Consequently the eigenvalue is (2n0−n1−n2+(n1−n2)√5)/2.

From `verification/`, running `python finite25.py` exactly tabulates the (n0,n1,n2) triples for all nonzero characters and proves the least nontrivial eigenvalue is at least −31/4, using only 2<√5<9/4. Hoffman's inequality then gives α ≤ floor(625·31/127)=152, which is strictly below 625/4. Indeed if I is independent then its indicator decomposes into (|I|/625)·1 and a zero-sum vector, and its adjacency quadratic form, which is zero, is bounded below using degree 24 on the constant component and −31/4 on the zero-sum component. This rules out four colors. Only the upper-bound check has been formalized in Lean here; the lower bound is an ordinary Fourier proof with a reproducible exact finite table.

## Initial finite graph search

The negative search is in the smaller field Q(√3,√11); that field plane is already known to need exactly four colors. These finite runs calibrate the search and say nothing new about the unrestricted six-versus-seven question. `rotation_search.py` performs exact rational generation and checking and uses python-sat for search. On rot=2/radius=2 it generated 60 directions, 1,801 points, and 7,044 edges. A 4-color SAT assignment was independently checked (re-run `python rotation_search.py --rotations 2 --radius 2 --k 4`). `direction_catalogue.py` enumerates all admissible directions at a given common integral denominator; checking weighted quadratic terms of each coordinate separately makes enumeration exact and fast. No candidate requiring five colors in this field was exhibited. In particular, this search is not an unrestricted lower-bound proof.

## Arbitrarily many radicals

`RadicalTower.lean` checks unit edges for an arbitrary list of nonnegative integer radicands with rational coefficients. The theorem `chromatic_lower_of_tower_witness` converts a finite, verified six-color refutation expressed in these coordinates into a seven-color lower bound for the plane. A three-radical unit-edge smoke test passed; a separate finite experiment with 5,833 vertices and 23,004 edges was four-colorable. No new unrestricted bound follows.

`Finite25Table.lean` additionally verifies the 24 unit directions, all 624 nontrivial Fourier frequencies, and the spectral arithmetic bound of −31/4. The spectrum identification and Hoffman argument remain ordinary proofs and do not assert a real-plane lower bound.
