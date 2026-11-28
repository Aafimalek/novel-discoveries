# Checked classification and disjoint-triple anchor adapter

`FranklPairDesignDeficitOne` proves the exact incident degree deficiency
identity for any pair design. If every degree is at least k−2, all
blocks have size two or three, triples are vertex-disjoint, the triple
count t obeys N+2t=choose(k,2) and 3t≤k, and each triple vertex has
degree k−2.

`FranklDeficitOneActualAnchors.exact_four_deficit_le_one_two_triple_anchors`
(namespace FranklForcingFiber) supplies the prior linked quotient's
explicit hypotheses automatically: under actual NoStrictMajority and
WeakMinimalGround, four isolates, degrees at least k−2, and a choice
of one anchor in each of two different triple blocks, all isolates
occur in the original pair avoidance maximum and deleting any one
of them gives another original avoidance member.

No contradiction or full deficit-one exclusion yet. The case of one
triple and the mixed-count step for multiple triples are separate.

Replayed with ordinary pinned Lean 4.36, one worker, 2500 MB memory
limit, warnings treated as errors, and overlay temporary storage.
Dependencies from the prior all-pair and linked quotient replays.
