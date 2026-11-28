# Verified arbitrary ambient trace classification

Two files compiled cleanly on pinned Lean 4.36.0 / Mathlib:
FranklFourAmbientTrace (arbitrary ambient labeling, exact
trace cardinality/frequency, and mask eligibility) and
FranklFourAmbientClassification (checked witness-or-15-profile
dichotomy, followed by the checked repair excluding the survivor).

The endpoint FranklForcingFiber.exists_containingTrace_witness_of_exact_four
guarantees a WitnessSpec for any hypothetical weak minimum-ground
one-source family with four isolates. It does not transport its
avoidance and chain data back to the original family; that next
step is needed to contradict the existence of such a family.

Successful workspace replay is recorded in replay.log. Both
stages exited zero, no warnings/errors, ten axiom audits
all [propext, Classical.choice, Quot.sound].

The extracted archive stores the exact 18 local Lean sources in
transitive import order and the Mathlib/Lean pins. To rebuild
outside this workspace with an already cache-built Mathlib checkout:

    set -o pipefail
    MATHLIB_ROOT=/abs/path/to/mathlib4 LEAN_BIN=/abs/path/to/lean \
      ./rebuild.sh 2>&1 | tee portable-replay.log

This portable source replay command was staged but not separately
executed in this wave; the verified replay imported the existing
pinned built dependencies.
