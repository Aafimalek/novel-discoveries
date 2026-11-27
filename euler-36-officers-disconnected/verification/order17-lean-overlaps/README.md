# Euler size 17: overlap clause blocks

This is a geometry-to-CNF result for the minimum-frequency-two branch,
not an additional SAT refutation.

- `EulerOverlapClauses.lean` interprets a signed overlap exclusion as a
  statement about used pairs and actual degree thresholds.
- `EulerOverlapCases.lean` proves an analytic obstruction: an unused
  low-low pair with two shared neighbors in one of the other coordinate
  groups has no shared neighbor in the last group. Otherwise saturation
  forces a 4×3 rectangle. The three vertices on the short side would have
  degree at least four; the other three vertices have degree at least two.
  This forces at least 18 placements.
- `EulerArchivedOverlaps.lean` generates the exact ordered clause blocks
  for the q2, double, one and zero variants and proves all clauses hold
  with the appropriate global invariant. It also includes an exhaustive
  non-normalized selection theorem: all low-low pairs used; some
  same-side double; no same-side double but some two-sided overlap;
  no double of either kind but some overlap; or an unused low-low pair
  and no overlaps.

The output of `EmitOverlaps.lean` can be compared to the original physical
DIMACS arrays with `compare_overlaps.py`. These are separate byte-level
audits, not theorems about a formal parser. This stage deliberately does
not certify pinned-word normalization within the cases, free-label
symmetry breaks, extra profile thresholds or any further SAT refutation.

## Reproduce

Use Lean 4.36.0 and its matching Mathlib. Compile the above three files
in order with the previously verified Euler support and cardinality
modules, `EulerGeometryValuation` and dependencies on `LEAN_PATH`.
Then run `lean --run EmitOverlaps.lean > emitted-overlaps.txt`.
With `python-sat==1.8.dev24`, run
`python compare_overlaps.py emitted-overlaps.txt PATH_TO_EXACT_SIZE_17_AUDIT`;
the input path is the archived parent containing the separate proof
family subdirectories and manifests.
