# Further Lean-checked height-six reductions
No claim of the unrestricted union-closed conjecture. These are conditional restrictions on ground-minimal hypothetical height-six counterexamples to strict majority, allowing equality at one half.

The modules were checked locally with Lean 4.36.0 and mathlib v4.36.0. All theorem audits in logs contain only propext, Classical.choice, and Quot.sound. The FewIsolates log has a harmless unused-argument lint. Files from the prior proof overlays are included to make imports available after an environment restart.

Suggested order in the lean directory (include that directory in LEAN_PATH alongside pinned mathlib and dependency libraries):
1. FranklForcingFiber, FranklHeightThreeSauer, FranklHeightThreeArithmetic
2. FranklCrossStarPair, FranklPairExtra, FranklPairSaturation, FranklStarIndex
3. FranklSaturatedPartners, FranklMultiLeafPair, FranklStarCounting, FranklProjection
4. FranklTerminalPairGeometry, FranklHeightFourSauer, FranklIsolatedWitness
5. FranklSharedIsolate, FranklLowFrequency, FranklFewIsolates
6. FranklAllIsolatedCounting, FranklAllIsolatedEdges, FranklOneIsolateCounting, FranklOneIsolateSmallSources, FranklWitnessCounting

Core new results:
- All-isolated: every active point occurs in at least 2n-1 members, giving at least 4n-2 members in total. Each point has a partner with a co-pair or a height-three avoidance fiber.
- One source: at least three isolates. Exactly one isolate and nonzero sources: at least nine sources.
- Every two distinct leaves have at least n+k-1 pair-avoiders, where k is source count. If k>=2 then leaves+sources <= choose(isolates+sources-2,2).
- Build FranklWitnessMultiLeaf last: a nonunary star with another nontrivial star requires at least four isolated points (stronger than the earlier three-point bound).

## One isolated point: exact avoidance maxima

[FranklOneIsolateOrdinaryLine.lean](lean/FranklOneIsolateOrdinaryLine.lean) builds from `FranklAllIsolatedEdges`. In a ground-minimal weak counterexample of height at most six, if there is exactly one isolate x and a forcing edge, some source p and its leaf s have the maximum set avoiding x and s equal to the ground with exactly x, p and s deleted. For a leaf t of a different source, the maximum avoiding s and t must contain x. The same module separately checks the projection result that erasing an isolate creates a strict majority at a leaf.

The [Lean axiom audit](logs/build-one-ordinary.log) contains only the three standard axioms. The many-source, one-isolate case is still open.
