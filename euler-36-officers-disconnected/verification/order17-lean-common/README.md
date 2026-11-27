# Actual geometric inputs to the exact size-17 cardinality blocks

These files concern the common cardinality components of the archived
minimum-degree-two size-17 Euler branches. They do not close another
SAT branch or complete the reduction for all geometric designs.

* `EulerGeometryCounters.lean` proves the geometric count theorems:
  every pair projection of a linear design has the placement count.
  The archived first projection, IDs 1297–1332, therefore has 17 ones.
  In each coordinate, each label has degree in 2–6 and the degrees
  sum to 17, so the 24 threshold inputs (degrees 3, 4, 5, 6 for each
  label in order) have exactly (17-6\times2=5) ones. This provides
  witnesses to each sequential counter in the existing checked model.
* `EulerCounterSlots.lean` proves the exact auxiliary offset and its
  inverse: the first two rows are interleaved `2*j+r`; later rows use
  `k*r+j`. It is not a row-major layout throughout.
* `EulerNumberedCounters.lean` defines the ordered signed clauses
  in the physical numbering and proves all of them hold under their
  model's input and state hypotheses.
* `EulerArchivedCounterValuation.lean` installs the ten disjoint
  grids in one numbered assignment and proves their complete physical
  clause blocks. The assignment preserves IDs 1–9072 (word, pair, and
  support-counter bits) and 9719–9886 (existing unary-degree bits).

## Local replay

Dependencies are the existing checked Euler `EulerSequentialCount`
and `EulerDegreeThreshold` modules plus their project imports. Build
the four files in the order listed above with the same Lean 4.36.0
and Mathlib. The axioms printed for the mathematical results are only
`propext`, `Classical.choice`, and `Quot.sound`.

With this dependency path, run `lean --run EmitCounters.lean` to emit
the Lean-defined ordered numeric clauses, followed by
`python compare_emitted.py OUTPUT ORIGINAL.cnf ...` to compare signed
literals against archived inputs. This byte comparison is separate
from the kernel proof of the clause semantics. An independent
allocation check `python audit_counter_slots.py ORIGINAL.cnf ...`
also reproduces the intervals from the closed numbering formula.

The original full-clause parser and the case-family-specific geometry
(normalization and remaining cuts) are not discharged by these results.

## Connected minimum-degree-two result

With `LatinGap` available, build `EulerRename` and `EulerAnchorNormalize`. These check the relabeling, preservation of size/linearity/saturation/degrees, and normalization of the anchor to `0000` for degree one, or `0000` and `0111` for degree two. Build `EulerMinTwoCommon` last, with [EulerGeometryValuation](../order17-lean-c06) and the numbered-count files on the module path. It combines geometric normalization, the abstract core, unary-degree clauses, and all ten exact-count grids in a single numbered valuation. The 2,812 count clauses were independently matched against each of the seven full formulas already refuted by Lean, using their exact SHA-256 hashes.

The [support assembly](../order17-lean-support-assembly) now constructs an assignment to the original support-AMO variables and proves simultaneous satisfaction of all 34,564 shared prefix and cardinality clauses. The remaining case-specific cuts, normalization into the full case list, and the other original refutations are not covered. This is not an end-to-end lower bound.
