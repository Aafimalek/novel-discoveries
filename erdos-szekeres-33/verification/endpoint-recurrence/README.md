# Lean-checked endpoint path recurrence for the ES33 residual encoding

`ES33/EndpointRecurrence.lean` checks the dynamic-programming state
interpretations underlying the compact Baek–Balko signotope search:

- `EndState` records the first vertex and the last two vertices of
  an increasing monochromatic chain (used for caps).
- `StartState` records the first two and the last vertex (used for cups).
- `forward_exact` and `backward_exact` prove that the corresponding
  recurrences compute precisely those chain-existence predicates, with
  state depth zero meaning length three.
- `ends_iff_forward` and `ends_iff_backward` prove exact projection
  to the two endpoint states; `ends_two_iff` proves the length-two base.
- On legal signotopes, `IsChain.all_signs` promotes consecutive
  homogeneity to all selected triples, and `Ends.shorten` removes an
  interior point while retaining the endpoints and color.

Plain Lean 4.36.0 with Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
checked this module. The audit reports only standard Lean axioms.
Copy the source under `ES33/` in the Lean project that provides
`ES33.EndpointPacket`, then run `lake build ES33.EndpointRecurrence`.

`ES33/EndpointModel.lean` verifies that the finite typed one-way structural
constraints are exact after projection of the auxiliary states.
`Propagation.cap_forced` and `Propagation.cup_forced` show that any
model must set every actual chain endpoint state, even though the
clauses do not require false positives to be absent.
`actual_propagates` gives a model using actual chain existence,
and `typed_model_iff_actual` proves equivalence of typed existential
satisfiability and the stated semantic endpoint exclusions for given
cap, cup and polygon thresholds. This module does **not** yet link the
chain pair criterion to general selected even sets, and does not
formalize omitted out-of-span state cells or DIMACS numbering.
Build `ES33.EndpointModel` after the recurrence module. The axiom
audit in `lean-model.log` uses only the standard three axioms.

The independent `ES33/EndpointGuardCore.lean` uses only the Lean core
`Lean` import. It restates the schematic auxiliary families in namespace
`ES33.EndpointGuard` and proves `pruned_iff_full_model`: span-capacity
guards do not change the existence of models. The missing cells can
be assigned false; the antecedent's interval capacity forces all
meaningful successor/projection/shortening references to stay in
range. Its audit has only `propext` and `Quot.sound`.
This module has a separate namespace; it is not an existing verified
import into `EndpointModel.lean` or a byte-level Python CNF certificate.
Build it with `lake build ES33.EndpointGuardCore` or with the same
pinned Lean executable alone.

This is the mathematical state semantics: it is not a verification of
the numbered Python DIMACS output or an UNSAT proof for 32 or 33 points.
