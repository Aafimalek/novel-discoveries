# Lean kernel proofs for all 33 extracted one-point-extension cores

This bundle covers the 33 insertion slots in the already checked
one-point-extension experiment for one fixed 32-point Erdős–Szekeres sign
pattern. For each slot, Lean 4.36.0 reconstructed a closed proof of UNSAT
for an exact extracted DIMACS core using the original variable numbers.
The Mathlib commit is `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, and the
reported axioms on each theorem are exactly `propext`,
`Classical.choice`, and `Quot.sound`. No native decision axiom or `sorry`
is used. The archive includes exact inputs, Lean source, and finite
proof traces for all slots.

The exact original 69,408-clause files and geometric assumptions are not
contained in the Lean theorem statements. The bundled independent Python
checker confirms that each core is a literal clause submultiset
of its corresponding exact original DIMACS. This core-containment check
and the specialization/numbering link to the geometric theorem remain
outside Lean. The geometric and abstract SAT interface is formalized
separately; this is not an end-to-end Lean proof of the full restriction,
and it is not a result about all 33-point configurations.

## Reproduce from the existing one-point-extension bundle

1. From the published extension bundle, regenerate the full DIMACS with
   `python3 extension32.py ./generated` and check them against
   `DIMACS.sha256`.
2. Use the Lean project pinned to Mathlib commit listed above. With its
   dependencies and compiled Mathlib available, run this from that project:

   ```sh
   bash /path/to/kernel-cores/verify_packaged_cores.sh /path/to/generated ./checked-cores
   ```

   This checks the archived files' SHA-256 digests, the exact clause
   submultiset independently, and each closed kernel proof. The script
   runs the Lean builds sequentially. An executable `LEAN` plus a
   suitably configured `LEAN_PATH` can replace `lake env lean`.

The extraction pipeline used
[DRAT-trim at 2e3b2dc0](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985)
to collect `-c` cores. For slots with non-RUP proof additions, a second
solve of the exact core with [Kissat 4.0.4](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.4)
in `--plain` mode generated fresh proof traces. Each converted with
`drat-trim -U -L` against the exact extracted core, which assigns the
initial LRAT clause IDs to core DIMACS positions. The Mathlib command
processes deletion ID lists and resolves positive proof hints by
clause ID; sparse addition IDs are fine. A proof against the original
DIMACS clause positions must not be reused against the shortened list.
The archive has proof-checker's finished LRAT, so a SAT solver or
DRAT-trim is **not** needed to replay the included kernel proofs.

`cases.tsv` records core sizes, original-replay versus fresh plain-proof
origin, and LRAT sizes.

A separate [rightmost-insertion pilot](../numbered-pilot) now verifies the exact full parsed formula and core containment in Lean for slot 32 only. The other 32 still use independent containment checks.
