# Checked conditional bridge to signed integer clauses

The three byte-exact files contained here were compiled on Lean 4.36.0,
one worker, warning-as-error, with temporary files on the overlay.
Their opening “static draft” comments are historical and were retained
to preserve the checked source hashes. Those comments do not assert that
the attached successful receipts are absent. No theorem was weakened.

  EndpointConcreteSpec     3.727 s    exit 0
  LiteralFamilies           1.559 s    exit 0
  RealLiteralConnector    40.221 s    exit 0

Highest stage max RSS 1,671,972 KiB. The two proof-local elaboration fixes
are in literal-elaboration.diff. All printed theorems use only propext,
Classical.choice, Quot.sound. Reuse the exact hash-matched NumberedCNF,
EndpointGuardCore, EndpointBaseAliases, RealResidualExtraction, and their
compiled dependency closures; compile these three source modules in the
displayed order. Matching predecessor and per-stage fingerprints are in
the JSON receipts.

What is checked: the literal shapes of eleven guarded endpoint families
and six local signotope clauses, the cap and cup length-three aliases,
and a forward satisfiability transport to the generic signed integer
compiler. For an actual real 32-point witness and a chosen valuation,
numbered_of_real_residual proves existence of a satisfying numbered
assignment under exactly:

1. Agreement of valuation sign bits with the real residual orientations.
2. PrunedPropagation P and PrunedExclusions X for its auxiliary states.
3. GoodRows, that each typed generated row is a matching guarded family
   or signotope packet.
4. Dictionary coverage for every literal of the generated typed formula.

Declarative row constructors and their local proof correspondence are
checked; the two metaproperties in items 3 and 4 are not proved in these
modules. Item 2 still needs the missing actual endpoint chain model
connection and geometric exclusions. This release also does not equate
the generic compiler result to an actual parsed external DIMACS object.
The independent computational guard audit (474,144 rows) remains a
cross-check, not Lean containment. No solver, UNSAT, or complete ES33
claim is made.
