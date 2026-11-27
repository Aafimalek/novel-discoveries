# Conditional Lean composition of all-used Euler geometry and SAT refutations

This package does not add SAT replays and does not assert that the
12-branch elimination is fully linked in the kernel.

* `EulerAllUsedConditionalRefutations`: a numeric model of the geometric
  clause list yields a zero-based Mathlib SAT model. A checked refuted
  subformula, with a checked containment proof, is enough to rule it
  out. Equality of the two formulas is a special case. This implication
  does not need a universal nonzero hypothesis: the witness in a
  satisfied numbered clause already appears at a nonzero literal.
* `EulerAllUsedTwelveConditional`: the 12 known refuted archive codes
  leave exactly the explicit five codes in `archivedRemainingFive`.
  The list complement is checked by kernel evaluation. The theorem
  `allUsed_geometry_only_five_given_links` combines the geometric
  theorem with this complement **under** per-branch containment or
  equality hypotheses. These hypotheses have not been discharged.
* `AuditArchivedDeclaration`: an independent check of the loaded
  formula declarations, not a proof-producing command. It evaluates
  the modeled list, recursively walks the actual balanced formula
  expression from the loaded proof module, expands aliases, and
  compares every ordered Mathlib literal expression against the exact
  reification of the modeled signed row. It checks that the selected
  existing theorem is of type `branchFullFormula.proof Sat.Clause.nil`.
  It adds no equality or containment theorem to the environment.

Use Lean 4.36.0 and matching Mathlib. For the first two modules put
`EulerAllUsedFullGeometry`, `EulerBatch.NumberedSemantics` and their
verified import closure on `LEAN_PATH`; compile in the above order.
Axioms are in the included logs. The external identity audit also needs
the already checked 12 refutation modules in `audited-branches.tsv`.
With those `.olean` modules already installed, compile
`AuditArchivedDeclaration.lean` and run the serial `audit_each.sh`.
No LRAT replay is required; the included script uses an executable
`check-replay.sh` entrypoint pointing to the configured Lean invocation
without rebuilding imports.

The missing kernel step is materializing 12 exact formula or
refuted-core containment proofs from the geometric generator to
the archived theorem types. The checked 12 original refutations and
the geometry-to-modeled-archive proof are separate until links are
checked. No exact minimum in Lean is claimed.

[Replay archive](euler-allused-conditional-composition-replay.tar.gz) · SHA-256 `7657e4627f2fe939e8754c04404ac03757c61fbe503e6266ebcf3d3397e5ff24`. The [independent identity audit](independent-identities.log) compared all twelve loaded declarations.
