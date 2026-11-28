# Exact guarded-clause audit of the anchored 32-label endpoint CNF

This audit independently checks the finite semantic-exhaustiveness part of
the concrete bridge. It is a **computational equality of clause content**, not
a Lean theorem, a SAT solver run, or a claim that the target is UNSAT.

For the anchored problem ((n,K,A,B)=(32,7,7,6)), it compares the guarded
clauses from their quantified mathematical conditions against the
previously pinned numbered DIMACS. The SHA-256 of that input is
`7f79b4e0e4186450489292b4cf823b75b0d85e7c70cae14d4ab0fbbf61cccd95`.
Use:

```sh
python3 audit_exact_guards.py /path/to/es32-anchor.cnf
```

If needed, regenerate the pinned DIMACS from the companion
`../numbered-endpoint-cnf/endpoint_dimacs.py 32 7 7 6 es32-anchor.cnf`.
No dependency on the generator is imported into the auditor.

The numbered wire contract allocates increasing triples for signs, followed
by cap pairs and states, then cup pairs and states. Within each family it
uses lexicographic labels and increasing allowed lengths. This is necessarily
the shared *layout* convention. The audit's expected clause enumeration is
independent: it quantifies the opposing lengths separately, processes both
extension colors from the same ordered quadruple, and groups pair and
projection rules differently from the exporter. It canonicalizes literal and
clause order with a bounded-memory external sort and proves file equality
by an exact byte comparison, preserving row multiplicities. It also checks
all sixteen sign assignments for the six-rule signotope packet.

In functional terms, each guard produces just one clause except the
length-three initialization rules, which become tautologies under the
already-checked aliases. The base-pair unit forces each pair state of
length two. The threshold unit denies the maximum length. Shortening
and projection require one antecedent; extension requires the old state and
the new adjacent signed triple. The cross-exclusion requires two available
pair lengths adding to nine and forbids both being true. The fixed 16-row
truth table makes the six packet clauses equivalent to at most one sign
change. Thus the external artifact provides a reproducible check of the
row-family content specified in the draft Lean bridge.

The additional `NumberedMatchesDraft.lean` states a simpler sufficient
formal contract: to transfer UNSAT, each solver-checked clause must occur
in the compiled specification up to literal order. This is the correct
containment direction. Exact order equality, equal duplicate counts and
exact external header bytes are unnecessary once the parsed checker object
and clause membership are formally bound. This short transport source is
**uncompiled**, and the concrete match remains to be proved in Lean.
