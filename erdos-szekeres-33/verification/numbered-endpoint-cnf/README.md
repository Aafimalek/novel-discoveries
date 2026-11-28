# Numbered endpoint-CNF groundwork for Erdős–Szekeres at 33

This is a checked modular increment, **not a proof that 33 points force a
convex heptagon**, and not an UNSAT result for its endpoint formula.

- `NumberedCNF.lean` proves that any finite typed Boolean CNF whose variables
  occur in a supplied ordered dictionary is equisatisfiable with its emitted
  signed-integer CNF. IDs are collision-free and between 1 and the dictionary
  length. A formal token format verifies the declared clause count, one
  terminal zero per line, and each literal's bound. For the compiler's
  output, parsing returns the exact original numbered rows. The theorem
  `of_checked_numbered_unsat` carries UNSAT about those exact rows to the
  input typed formula. These proofs use only standard Lean axioms and do not
  use `native_decide`.
- `NumberedAudit.lean` checks exact headers, literal IDs, polarity, row
  tokens and proof transport for a contradictory 3-cap projection with two
  unit clauses. Lean computes the exact two-variable formula, reads its exact
  three rows, directly proves numbered UNSAT, and transports it to the typed
  formula. This is a small audit, not a 32-label proof.
- `EndpointBaseAliases.lean` uses the previously checked
  `EndpointGuardCore.lean`. It proves that guarded endpoint models can
  replace their separate length-three triple states with the orientation sign
  (positive for cups and negative for caps), without changing
  satisfiability. All length-two and length-three *pair* states stay indexed.
- `endpoint_dimacs.py` explicitly lays out typed variables, emits numbered
  rows and optionally compares every row and every output byte to
  `etv_signotope` in Baek–Balko's linked code. It is an independently
  written regeneration, not a copy of upstream source. The asymmetric
  residual for a positive anchor on 33 points uses 32 remaining points,
  no 7-cap, no 6-cup, and no opposite chain pair making a 7-gon.

| Formula | Variables | Rows | Literals |
|---|---:|---:|---:|
| 9 labels / pentagon sanity instance | 466 | 1,800 | 4,646 |
| **32 residual labels, cap 7 and cup 6** | **37,365** | **474,144** | **1,375,738** |
| 33 unanchored labels, cap 7 and cup 7 | 45,210 | 570,880 | 1,656,968 |

The experiments matched the upstream byte stream
[pinned at `61bfbd6f04d73865a5037b0a416d5ba18ce34fbd`](https://github.com/jcpaik/erdos-szekeres-sat/tree/61bfbd6f04d73865a5037b0a416d5ba18ce34fbd).
The pinned source file hashes and generated DIMACS hashes are included.
Replay with standalone Lean 4.36.0 and Python 3:

```bash
bash check.sh /path/to/lean /path/to/EndpointGuardCore.lean /path/to/generated
# Optionally append /path/to/pinned/upstream to rerun upstream comparisons.
```

**Remaining link.** The Python generation and its exact byte comparisons are
computational checks, not Lean theorems. Still needed: Lean proofs that a
concrete generated typed clause list exhausts all guarded propagation,
exclusion and signotope families, and that the independently supplied
DIMACS bytes tokenize to the same exact object. The verified generic
compiler/roundtrip theorem does not assert either of those facts about
arbitrary external files. No long SAT run was started.
