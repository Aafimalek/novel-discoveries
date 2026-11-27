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
- One source: at least three isolates. Exactly one isolate and nonzero sources: at least fourteen sources in Lean (see below).
- Every two distinct leaves have at least n+k-1 pair-avoiders, where k is source count. If k>=2 then leaves+sources <= choose(isolates+sources-2,2).
- Build FranklWitnessMultiLeaf last: a nonunary star with another nontrivial star requires at least four isolated points (stronger than the earlier three-point bound).

## One isolated point: exact avoidance maxima

[FranklOneIsolateOrdinaryLine.lean](lean/FranklOneIsolateOrdinaryLine.lean) builds from `FranklAllIsolatedEdges`. In a ground-minimal weak counterexample of height at most six, if there is exactly one isolate x and a forcing edge, some source p and its leaf s have the maximum set avoiding x and s equal to the ground with exactly x, p and s deleted. For a leaf t of a different source, the maximum avoiding s and t must contain x. The same module separately checks the projection result that erasing an isolate creates a strict majority at a leaf.

The [Lean axiom audit](logs/build-one-ordinary.log) contains only the three standard axioms. The many-source, one-isolate case is still open.

## One isolated point: omitted-star block counting

The Lean theorem `one_isolate_nonzero_sources_ge_eleven` in [FranklBlockWitnesses.lean](lean/FranklBlockWitnesses.lean) raises the checked lower bound from nine to eleven sources when there is exactly one isolated point and a forcing edge. The lower bound counts additional pair-avoiding witnesses using the blocks formed by the pair-avoidance maxima. In the pre-existing Lean import environment, check these new modules in order: `FranklBlockIncidence`, `FranklOmittedStarBlocks`, `FranklBlockWitnesses`. The [independent replay log](logs/FranklBlockWitnesses.log) lists only the three standard Lean axioms.

The [written proof](paper/one-isolate-block-closure.md) ([PDF](paper/one-isolate-block-closure.pdf), [TeX](paper/one-isolate-block-closure.tex)) raises the one-isolate bound to fourteen by considering which blocks can be omitted together. The complete fourteen-star lower bound is Lean-checked below. The [arithmetic checks](paper/check-block-arithmetic.py) are also reproducible independently. Other isolate counts and the unrestricted height-six statement are not resolved.

### Excluding eleven stars in Lean

[FranklExcludeElevenStars.lean](lean/FranklExcludeElevenStars.lean) proves `one_isolate_nonzero_sources_ge_twelve`. It counts links between stars outside a three-star block, then bounds pair avoidance by encoding each set using the distinct membership signatures. Check the new modules in order: `FranklElevenStarStructure`, `FranklTripleDegree`, `FranklTripleLinks`, `FranklFiberSignatures`, `FranklExcludeElevenStars`. The [axiom log](logs/FranklExcludeElevenStars.log) and [source hashes](lean/exclusion-eleven-source-sha256.txt) record the independent replay.

### Excluding twelve stars in Lean

[FranklExcludeTwelveStars.lean](lean/FranklExcludeTwelveStars.lean) proves `one_isolate_nonzero_sources_ge_thirteen`. Both the four-star-block case and the case with all blocks of size at most three are checked. After the previous modules, compile `FranklBlockClosureEncoding`, `FranklFourBlockGroups`, `FranklNineSignatureMatching`, and `FranklExcludeTwelveStars`. The [axiom log](logs/FranklExcludeTwelveStars.log) and [source hashes](lean/exclusion-twelve-source-sha256.txt) record the independent replay.

### Excluding thirteen stars in Lean

[FranklExcludeThirteenStars.lean](lean/FranklExcludeThirteenStars.lean) proves `one_isolate_nonzero_sources_ge_fourteen`. The size-five, size-four, and triple-only branches for thirteen stars have all been checked. After the previous modules, compile `FranklNineOutsiderGroups`, `FranklDenseSignatureCounts`, `FranklThirteenDegreeMoment`, and `FranklExcludeThirteenStars`. The [axiom audit](logs/FranklExcludeThirteenStars.log) and [source hashes](lean/exclusion-thirteen-source-sha256.txt) record the independent replay. The fourteen-or-more case and the general height-six statement remain open.
