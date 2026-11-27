# Exact anchored all-used CNF prefix before free-label lex symmetry

This package supplements the prior 50,146-clause common, pin/profile,
and rectangle result. It places the 6,888 unary-degree table clauses,
the original finite suffix **degree** ordering, and the original second
1,296-clause saturation block in their physical positions, in one
numbered valuation. The candidate rectangle propagation block is the
last modeled sequence. The earlier coarse anchored-base rectangles
generate no clauses at size 17/minimum two.

`actual_allUsed_nonLex_holds` reasons about a normalized actual design and
the same numbered valuation as the previous proof. The degree order is
sound because the exact profile is monotone: label zero has degree two,
and all other labels have degree three. `allUsed_geometry_nonLex` derives
the profile and a matching published diagram solely from a hypothetical
linear saturated size-17 design with all degrees at least two and all
low-low pairs used.

To reproduce, use Lean 4.36.0 with matching Mathlib, place the verified
`EulerMinTwoCandidateAssembly`, `EulerAllUsedProfilePreserved` and their
dependencies on the Lean path, and compile files in source order. The
included logs record the standard-only Lean axioms. Separately,
`lean --run EmitNonLex.lean > emitted-nonlex.txt` followed by
`python compare_nonlex.py emitted-nonlex.txt PATH_TO_ALL_USED_ARCHIVE`
with `python-sat==1.8.dev24` compares the exact signed clause arrays
against independently hash-verified original DIMACS files. That is
an independent external exact check, not a Lean parser proof.

The theorem deliberately stops before the final free-label
lexicographic symmetry clauses. It proves neither a whole-CNF
valuation nor a Lean refutation of any additional case, and does not
prove the global exact Euler minimum in Lean.

## Frozen replay closure

The 41 local Lean source dependencies are included under
`lean-source-closure/`. They are supplied in the same transitive order
used by the successful local builds, in `local-build-order.txt`, and
their hashes are in `lean-source-sha256.txt`. A clean replay command is:

```sh
# Supply Lean 4.36.0's executable and compiled upstream Mathlib dependencies.
# LEAN_PATH must already include upstream Mathlib and its dependencies.
LEAN_BIN=/path/to/lean ./replay_lean.sh
```

The latest local checks used successfully compiled local imports, not
a fresh rebuild of all 41 dependencies from this tarball. The checked
prefix lengths across all 17 originals are 58,350 to 58,370 clauses.
The remaining lex suffix lengths are 1,260 to 2,835. The audit log gives
the exact per-file prefix length, suffix length, original DIMACS SHA-256,
and SHA-256 of the exact prefix clause rows (LF-joined with terminal LF,
excluding the header). Every modeled row matched byte for byte after
trimming outer whitespace, preserving literal order and signs.

[Replay archive](euler-allused-nonlex-replay.tar.gz) · SHA-256 `ae28f0ac164c02f310219fa46d2de9f71f61818c9789f4422a1ff218f286893b`.
