# Verified complement, pair-atom, and isolate-omission transport

The three source modules compile on the pinned Lean 4.36.0 and
Mathlib toolchain, one worker with a 2500 MB cap and workspace
overlay TMPDIR. The final audit is replay.log. All fifteen
printed theorem audits use only propext, Classical.choice, and
Quot.sound. No native oracle or placeholder is used.

Scope:

1. **FranklTrueComplement** checks exact complement membership,
   cardinality, De Morgan closure and reversal of strict chains.
   The true support is the ground of a nonempty union-closed
   family. On that support the complement family has its empty
   member and the exact hypotheses of the generic atom and
   saturation results.
2. **FranklPairAtomBridge** transfers those results to
   compressedStarPair for any two distinct sources of a weak
   ground-minimal family. Its actual true support is exactly all
   nonomitted centers and the isolated points present in the
   pair maximum. The atom-sensitive bound is stated in the raw
   leaf-pair avoiding fiber's cardinality. An arbitrary relative
   omission has a physical avoiding preimage with the specified
   representative trace.
3. **FranklPairIsolateOmissionLift** checks that an isolate-only
   true-support relative omission is the raw pair maximum
   minus exactly those isolate points, as an actual raw fiber
   member. The proof does not assume saturation of all isolates
   or that other stars are unary.

The bundled source archive lists the local dependencies in import order.
To replay, extract to a fresh directory and run
`MATHLIB_ROOT=/path/to/pinned/mathlib4 LEAN_BIN=/path/to/lean bash rebuild.sh`.
The three newly verified files used the pinned built dependencies for
the recorded run; the full portable source order has not separately
been rebuilt for this release.

Still **not** checked here: mixed-witness disjointness/counting,
the constant-signature quotient cases for deficits one and two,
the full exactly-four multi-source exclusion, or the universal
at-least-five theorem. These modules are exact intermediate
results for those proofs.
