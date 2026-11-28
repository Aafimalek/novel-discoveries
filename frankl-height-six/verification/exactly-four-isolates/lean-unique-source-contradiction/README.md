# Checked exactly-four-isolate single-source exclusion

The two modules were compiled on pinned Lean 4.36.0 and Mathlib,
importing the independently rebuilt 18-module ambient classifier
closure at frankl-ambient-portable-fresh/build. The final guarded
replay exited zero for both stages, without warnings or errors.
All eight public axiom audits list only propext, Classical.choice,
and Quot.sound.

The endpoint

    FranklForcingFiber.unique_source_not_exact_four_isolates

takes NoStrictMajority G, WeakMinimalGround G, a source p that is
the unique source, and (isolated G).card = 4, and concludes False.
The certificate, its transportation to arbitrary ambient traces,
the witness's actual avoiding support and height-two upper bound,
and the actual co-leaf incidence lower bound all appear in the
verified dependency closure. The exceptional numerical profile is
excluded by the previously verified one-step repair. There is no
additional mathematical input at this endpoint.

This verifies the single-source branch only. It does not prove
the multi-source branch or the at-least-five-isolates bound in
Lean, and it does not solve the unrestricted height-six problem.

Workspace audit command:
    set -o pipefail
    ./check-avoidance.sh 2>&1 | tee replay.log

To append to a portable pinned source rebuild, copy these two
source files into the verified ambient bundle's sources directory
and append FranklFourAvoidanceGeometry then
FranklFourAvoidanceIncidence to dependency-order.txt. Regenerate
its source digests and run its pinned one-worker audit command.
No native code oracle is used. The earlier failed attempt is
for local diagnostics only and is not part of the final audit.

The archive supplements the 18 ambient-classifier modules with these
two completed proof modules. To replay, extract the archive into a
new directory, verify `sha256sum -c sources.sha256`, then run
`MATHLIB_ROOT=/path/to/pinned/mathlib4 LEAN_BIN=/path/to/lean bash rebuild.sh`.
All 18 dependencies were freshly rebuilt; both new files were then
built against those objects. The bundled dependency order preserves
this schedule and ends at the one-source contradiction.
