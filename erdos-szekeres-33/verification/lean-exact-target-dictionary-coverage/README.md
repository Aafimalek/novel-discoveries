# Checked whole-dictionary coverage

The static draft source was strict-checked unchanged. `ActualCoverage.lean` imports
previously strict-checked `CoverageInequalities` and uses the checked
constructor exhaustiveness result `actual_goodRows`. Its proved conclusions
are `actual_covered n K A B hA hB` (where `2 ≤ A` and `2 ≤ B`),
`target32_covered : covered 32 7 7 6`, and conditional
`target32_numbered_of_guarded`.

The proof walks *every* literal position in each of the eleven typed rule
families and each of the six packet rows. A flipped literal retains its key.
Pair thresholds use their `PairFits`; the shortened length retains both
limit and span by monotonicity. Projection from a triple uses the checked
width inequality. Each extension stays ordered by transitivity, obeys its
side limit by its declared guard, and uses a span that grows by at least one.
Length three aliases the sign key with the appropriate polarity. The six
packet rows refer only to the four strictly ordered triples from the
quartet. Cross thresholds use each pair guard separately. Nothing about
actual propagation, exclusion, geometry, or externally serialized bytes is
assumed in coverage.

Strict replay ordering: verify the two receipts and their prerequisite
hashes under `es33-goodrows-check/release`, then compile this module using
`es33-goodrows-check/out`, `es33-literal-bridge-check/out`, and
`/tmp/es33/numbering-core/clean-room` as the Lean path, as appropriate in
the original workspace. A successful build must produce the three printed
axiom audits without nonstandard axioms. In a fresh overlay with `out/` and
`tmp/` run `python run_stage.py ActualCoverage 75`, then run
`python run_stage.py ActualRealConnector 100` for the conditional real
orientation connector. The runner pins the Lean executable and uses a
single worker, strict warnings, 2250MB Lean cap and 2310000KiB RSS cap.
Both passes have SHA-pinned receipts; see JSON files.

`ActualRealConnector.lean` specializes the prior real-witness connector
to the closed structural results. Its explicit remaining conditions are
`onSigns`, `PrunedPropagation`, and `PrunedExclusions` for the
particular valuation. The resulting SAT claim is only for the exact
compiled in-Lean object, not the external target.

## Remaining semantic and exact-object links

- For any real residual witness, construct one valuation over
  `EndpointVar`: the sign keys are its real orientation bits, and each
  auxiliary key encodes actual chain existence (`EndState`, `StartState`,
  `Ends`; cap false and cup true). `ES33.Endpoint.actual_propagates` is
  already checked for a signotope but uses its own `States` and
  `Propagation` definitions. Transfer it to the GuardCore
  `PrunedPropagation` used here. Non-length-three states agree by the
  valuation definition; length-three aliases agree with actual chain
  existence only under the relevant ordered-triple guards, via
  `end_base` / `start_base`. Do not assert blanket agreement at unordered
  triples, which need not hold.
- Under the chosen valuation, prove `PrunedExclusions 7 7 6`. A
  seven-cap is a forbidden all-negative even seven-set; a six-cup is the
  forbidden all-positive six-set from the anchor; common-endpoint opposite
  chains with sizes summing to nine must yield an even seven-set. The draft
  `EndpointPolygon.lean` contains this idea in the intended
  `exclusions_7_7_6_iff`. Only the direction from residual avoidance to
  actual exclusions is needed for target UNSAT. `EndpointSubsets` and
  `EndpointPolygon` remain unchecked; use the already checked real-to-
  residual orientation reduction for the geometric premise.
- To use an external UNSAT checker, prove that its exact loaded signed
  object matches the compiled target: ideally
  `content32 t target32_covered`, or the sufficient one-way
  `Matches checkerFormula compiledTarget` from the checked transport.
  Clause/variable counts, a SHA, and an external byte/multiset audit are
  reproducibility evidence, not this Lean theorem. The reflection-lex
  augmented formula additionally needs its own numbered auxiliary/row
  link; this package concerns the unaugmented base CNF.
- Finally the target itself still needs a checked UNSAT certificate
  (or a valid geometric witness for a counterexample). This package proves
  neither outcome.
