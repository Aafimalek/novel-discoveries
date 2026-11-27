# Euler all-used geometry to exact finite table

This package extends actual outer-word normalization to the precise
finite table input. Compile in the order in `verified-sources.txt`
with Lean 4.36.0 and matching Mathlib, and with the existing
`EulerAllUsedFrequencies` and `EulerNormalizePattern` module
dependencies on the Lean path.

- The actual design is renamed to central word 0000 and its four
  distinct one-low words.
- Its columns are verified to be in the exact five-pattern list.
- The matrix assembled by `ofColumns` has exactly the same 16 entries
  as the outer words of that design. Geometric linearity checks
  the exact Boolean `oneOverlap` filter.
- After `canonical`, the resulting list is proved to be a member of
  the exact finite output `cases`.

`EulerAllUsedDiagramData` consists of the exact definitions separated
from the independently built arithmetic audit for convenient modular
checking. This package does not claim that `cases = published` is
kernel-checked. It also does not yet transport the specific selected
canonical permutation and ranks physically into a final renamed
design. The axiom audits of all exported geometry and table theorems
are standard.

The included `EulerNormalizePattern.lean` supplies the general first-occurrence relabeling theorem, using `EulerRename` from the [previous common package](../order17-lean-common). Compile it before the three modules listed below or in `verified-sources.txt`.

## Kernel-checked published list coverage

Compile `EulerAllUsedDiagramShards.lean` after `EulerAllUsedDiagramData`. Its 25 exact checks cover all choices of the four column patterns. `validInput_is_published` proves every canonically encoded candidate that passes the one-overlap filter belongs to the 17-diagram published list. This is a coverage implication, not a claim that every listed pattern is geometrically realized. Realizing the canonical coordinate permutation and applying the complete family of original SAT refutations are still separate.

Build `EulerActualPublishedDiagrams.lean` last. Its theorem `all_used_actual_published` combines the actual geometry with the kernel-checked enumeration: the canonical encoding belongs to the 17 published diagrams, and an explicit entry of the permutation list attains it. The physical realization is now checked as described below; the translated branch formula remains separate.

## Actual relabeling and word codes

# Actual Euler all-used designs and the seventeen archived diagrams

Use Lean 4.36.0 and matching Mathlib. This continuation assumes the
checked `EulerActualOuterTable` replay and `EulerAllUsedDiagramShards`.
The latter is the separate standard-kernel check of canonical table
coverage. Both use the same `EulerAllUsedDiagramData` definitions.
Compile in the provided source order.

- `EulerActualPublishedDiagrams`: the actual normalized design's
  canonical matrix belongs to the published table, and an actual input
  index list achieves that canonical result.
- `EulerActualCoordinatePerm`: that index list is a true coordinate
  equivalence, and its geometric implementation transports all four
  outer placements and their entries.
- `EulerActualSymbolRanks`: independently relabel the actual symbols in
  each column, preserving zero, to realize the rank numbering.
- `EulerActualDiagramRealization`: the resulting four actual member words
  have decimal codes in the published seventeen-diagram list, with all
  linear, saturated, size, central word and frequency-two zero
  hypotheses explicitly carried through.

This package handles the geometric case selection on the all-used branch,
not the remaining CNF clauses or SAT refutations.
