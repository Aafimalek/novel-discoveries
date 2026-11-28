# Lean verification of the real nine-weight lower bound 149

The final theorem is `NineSeparatedSubsetSums.separated_nine_at_least_149`.
It applies to any nine positive real weights, with no ordering or
integer assumption. If all distinct labeled subset sums differ by
at least one, at least one weight is at least 149. This does **not**
identify the exact real optimum. The independent integer witness at
161 gives the other end of the current range.

## What is checked

The real bridge forces a hypothetical maximum below 149 into the
exact integer cap 148. The previously checked integer certificates
cover all allowed second-largest weights through 147; the final
assembly discharges the entire range and makes the real theorem
unconditional within its stated hypotheses. See:

- [Generic range dispatch](GenericAssembly147.lean)
- [Full real theorem](LowMemoryRealAssembly147.lean)
- [Independent theorem and axiom audit](AuditLowMemoryRealAssembly147.lean)
  and [its full output](audit.log)

The proof uses only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms. There is no `sorryAx`, native-computation
axiom, or project-specific axiom in the final theorem.

The written paper uses the published integer optimum, while the
formal theorem verifies the exclusion needed at cap 148 within Lean.
The proof modules were checked on the pinned workspace, and the
final assembly and separate audit both loaded those objects.
The distributable archive below contains the entire local source
dependency closure, not prebuilt object files. We have not yet rerun
every module from a completely empty extracted directory.

## Replay from source

Use Lean `4.36.0` and Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` with its matching dependencies.
Obtain the parts of the source archive in the `source-parts/` directory
in sorted order. Check `SOURCE_PARTS.sha256` and reconstruct:

```sh
sha256sum --strict -c SOURCE_PARTS.sha256
cat source-parts/source-*.part > lean-real-149-source.tar.gz
sha256sum --strict -c SOURCE_ARCHIVE.sha256
mkdir lean-real-149-source
tar -xzf lean-real-149-source.tar.gz -C lean-real-149-source
cd lean-real-149-source
MATHLIB_LEAN_PATH=/absolute/path/to/compiled/mathlib-and-dependency-library-dirs \
  bash replay-clean.sh
```

Provide the colon-separated Lean library directories for the pinned
built Mathlib and all its dependencies as `MATHLIB_LEAN_PATH`. The
replayer checks SHA-256 and the exact source import order, compiles
the modules serially, and writes the final theorem and its axioms to
`replay-logs/final-audit.log`. This is a long rebuild; the frozen
source closure contains 10,440 Lean files including the final audit.
No Codex was used.
