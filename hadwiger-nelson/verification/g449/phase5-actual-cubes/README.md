# G449: verified graph rotation and central-neighbour cycle

Attribution: Heule and Przybocki's [G449](https://github.com/bprzybocki/G449/tree/125bfda97ed1d336f84694de04dedcfb349c5164), accompanying [From two heptagrams to a 449-vertex 5-chromatic unit-distance graph](https://arxiv.org/abs/2611.28518). These modules verify the automorphism of their graph and do not claim novelty for the graph or its rotation.

Reproduce with official Lean 4.36.0: use the previously audited pinned data directory containing G449.k21, G449.s6 and the independently regenerated edges.json. Use the phase3 arithmetic compilation directory containing AllPublishedEdges.olean and its dependencies. Run ./build_rotation.sh with absolute paths to those two directories. The script generates the concrete local data and 28 small certificate modules. No third-party input or source is redistributed here.

- G449_rotation_automorphism, together with rot_inv_on_published_vertices, shows the concrete rotation is a permutation of the 449 vertices preserving and reflecting adjacency on the entire published edge list. The adjacency lookup is kernel checked against the original 2,198-entry pair list.
- G449_central_neighbors_complete and G449_central_neighbors_cycle show the ordered seven distinct neighbours of fixed source vertex 228 are exactly the rows [9, 173, 170, 401, 181, 187, 410] and show how rotation advances them. The theorem G449_central_neighbors_independent also checks there are no edges among the seven.
- G449_rotation_coordinates checks all 12 exact coefficients at every rotated source row against the previously formalized integer spin map for multiplication by the sixth power of the primitive root.
- RotationPowers.lean checks all powers preserve adjacency and proper four-colourings, fix the center and advance ring slot i to (i+r) mod 7. This is the convention used by the previously checked finite orbit coverage.

The plain Lean axiom audits are provided. No CaDiCaL branch proof, LSR proof or new plane bound is claimed.

## Exact normalization into one of the six numbered cubes

Optionally pass the preceding pilot's compiled FiniteCaseCoverage module directory as the third argument to build_rotation.sh. The following checked theorems perform the composition:

- WordCoding verifies that the base-3 encoding decodes exactly at each of the seven positions.
- NormalizeColour verifies relabeling the center to color 0, composing by the actual graph rotation, and permuting the remaining three colours. A proper four-colouring can always be transformed into one of the six allowed branch words while retaining properness and keeping the center at color 0.
- TypedCubes checks the typed units and the exact six numerical lists of DIMACS singleton clauses, including omitted free slots and the negative units represented by minus signs. Its main theorem shows the normalized proper colouring satisfies the selected cube and the branch's allowed-word predicate.

- BaseCubeLift connects the labelled graph to the already-audited exact base DIMACS. If that formula had a model, a normalized assignment would model the same base plus one of the six numbered cubes and land in its allowed word.

These theorems do not assert that any branch is satisfiable or unsatisfiable. Full branch-formula attachment (triangular hints and exclusions as exact numbered clauses) and checked branch refutations remain separate.
