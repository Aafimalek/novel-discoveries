# Lean work in progress

This branch targets two local steps, not the nine-number theorem.

- `exists_prefix_near_double_sum`: the discrete prefix lemma underlying the step that moves a candidate collision toward the central rank interval in the 149 proof.
- `rounding_injective`: the final rounding implication of the earlier 148 + 1/6 argument, with the fractional error and collision-cardinality estimates given as hypotheses.

The GitHub workflow runs `lake build`. Pending checks do not count as verified. The critical solid slab, Harper cut, and integer exclusion are not formalized here, and neither bound has an end-to-end Lean proof in this branch.
