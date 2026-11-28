# Lean-checked actual mixed witnesses for the four-isolate project

The three source files compile on pinned Lean 4.36.0 and Mathlib
fc4f59e577feb1a4956671bc04ac18aaaf8cd842. All twelve theorem
audits use only propext, Classical.choice and Quot.sound.

The first file forms a genuine family member by unioning two
ordinary pair omissions in the unary-star case. It tracks
isolates missing from the true support before intersection.
The second proves these mixed witnesses are distinct by source
and hole, and cannot be any of the counted avoidance, source
witness, or pair-maximum members. The checked counting endpoint,
`FranklForcingFiber.leaf_pair_count_with_blocks_and_mixed`,
adds the size of any supplied finite set of valid mixed witnesses
to the existing source and block lower bound, with no overlap.

The numeric specialization of the baseline, existence of the
required mixed witnesses in every subcase, and the complete
multiple-source theorem are not established here. The archive
has the exact local sources in dependency order; extract and
run `MATHLIB_ROOT=/path/to/pinned/mathlib4 LEAN_BIN=/path/to/lean bash rebuild.sh`.
The recorded job checked the three new files against already
built prerequisites, not a fresh replay of this complete archive.
