# Additional C06 kernel refutation

The [replay archive](euler-c06-verified.tar.gz) proves that the complete original numbered branch `all-low-pairs-used/aus-0111_1012_2201_1220` is unsatisfiable. It checks the ordered containment of its 3,843-clause proof core in all 60,886 original clauses with original numbering. `Euler.Batch.C06.branchNoAssignment` depends only on `propext`. Use the same pinned Lean and Mathlib as [batch 1](../order17-lean-batch1), then run `bash replay.sh` after unpacking. The archive SHA-256 is `fd7f9db2b12ae4815cc687287fdd57d1bdb47299469b1bac6d8033673d42331d`.

With [batch 1](../order17-lean-batch1) and the [first pilot](../order17-lean-full-numbered), this is the seventh of the 56 original normalized size-17 inputs refuted in Lean. It does not prove that a geometric counterexample maps to one of the archived inputs, nor does it cover the other inputs.

The separate `EulerGeometryValuation.lean` constructs the shared word, pair and degree bits for a linear design and proves they satisfy the degree and rectangle clauses under the appropriate geometric hypotheses. Compile it after [EulerRectangleCut](../order17-lean-rectangles). Sequential auxiliary and branch-specific assignments remain separate. `rect-extra-audit.log` independently matches all 216 rectangle rows in each of four original degree-one formulas; this audit does not refute those formulas.
