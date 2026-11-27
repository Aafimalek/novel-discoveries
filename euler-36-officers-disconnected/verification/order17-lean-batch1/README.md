This [replay archive](euler-batch-checked.tar.gz) contains the sources, certificates, exact input and checked logs. Archive SHA-256: `3d91f9a7115b9922ccd341e3b4a13f7d1ee39404eb7a1a1438ca779b016c3628`.

Together with the [first pilot](../order17-lean-full-numbered), **six out of 56** original size-17 numbered inputs now have complete plain Lean refutations. This does not yet close the geometric lower bound.

# Additional original Euler size-17 refutations

This bundle kernel-checks **5** original size-17 CNFs,
in addition to the separately published pilot. Each `branchNoAssignment`
theorem concerns the complete formula, not merely the active core.
The branches and exact dimensions are listed in `checked.tsv`. Each
original's raw SHA-256 and its generator's regenerated native DRAT
hash were compared to the published original manifest before packaging.

The common proof driver parses DIMACS/LRAT as untrusted elaboration
preparation and emits checked Lean proof terms, factoring each RUP
step into a separate theorem. The second driver submits ordered-clause
inclusion proofs, from the core into the balanced complete original
formula; the kernel then transfers the empty-clause refutation.
All checked original refutations depend only on `propext`.
Nothing invokes `native_decide`.

## Replay

With Lean 4.36.0 and the matching prebuilt Mathlib dependencies on
`LEAN_PATH`, run `bash replay.sh`. The script decompresses and hashes
the original DIMACS before checking each branch. The compressed original,
core and LRAT suffice; no SAT solver is required. Larger refutations
can take up to a few minutes on a moderately provisioned machine.

Optional `WITH_NUMBERED=1 bash replay.sh` also compiles
`NumberedSemantics.lean`, assuming `EulerNumbering` and its symbolic
dependencies are on `LEAN_PATH`. It verifies that one-based signed
DIMACS clauses have exactly the same semantics under the zero-based
`Sat.Valuation` used by the refutations. Any included
`SymbolicToKernel.lean` additionally maps every typed symbolic clause
to this semantics. This is not a proof that a hypothetical design
satisfies every full archived branch: the remaining case-specific
geometric hypotheses and numbered joins are not discharged here.

The optional Python audit `audit_degree.py PATH` compares the 6,888
unary-degree clauses with the physical DIMACS slice 33047..39934 of the
minimum-degree-two originals, separately from Lean. It does not replace
a proof of this slice's relationship to geometry.

## Scope

These are only the listed normalized cases, not all 56. They do not
prove the full lower bound in Lean. The parser is used at elaboration
to produce an explicit kernel formula; this bundle does not formalize
DIMACS byte parsing as an independent input specification. The original
publishing manifest and hash checks identify the exact physical input.
