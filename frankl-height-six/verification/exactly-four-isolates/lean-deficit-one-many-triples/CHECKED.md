# Checked deficit-at-most-one, multiple-triple branch

`FranklDistinctTripleMixed` certifies two independent link deletions
and the k-coordinate Sauer upper bound at distinct-triple anchors;
it also proves the reverse bridge from an actual raw singleton
isolate deletion, on full isolate support, to an allowed hole.

The endpoint `FranklForcingFiber.exact_four_deficit_le_one_not_many_triples`
in `FranklDeficitOneManyTriples.lean` assumes actual NoStrictMajority
and WeakMinimalGround, exactly four isolates, all source degrees at
least k−2, and at least two distinct triple blocks. It proves False.
The t disjoint triples cover 3t sources; at fixed distinct-triple
anchors, the checked mixed-omission theorem and the independent product
of exterior triple sources with the four isolate singleton holes
supply 4(3t−2) extra witnesses. Added to the standard counts, this
forces a family of more than H(k) while the actual quotient cap is H(k).

This does not exclude the single-triple branch or higher deficits.
Pinned direct Lean 4.36, one worker, memory limit 2500 MB, warnings
as errors, overlay temporary storage. The receipt checks the two new
modules against prior checked local dependencies.
