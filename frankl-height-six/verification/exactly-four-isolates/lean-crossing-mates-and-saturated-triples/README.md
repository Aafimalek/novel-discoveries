# Lean-checked crossing mates and saturated four-triple configurations

These two lemmas check separately under strict Lean. Neither theorem says
the configuration occurs in, or is excluded from, an actual Frankl
counterexample. The actual-family adapter remains unverified: after the
initial run was interrupted, a separate attempt stopped at Lean's
deterministic heartbeat limit. The noncycle construction was not run.

See CHECKED-PARTIAL.md for scopes and the successful module logs for
standard axioms. The module headers are unchanged from the static draft;
the corresponding logs and checked hashes are the final check receipts.

The first module imports FranklLinkCliqueRegions from the [pinned
previous source closure](https://github.com/Aafimalek/novel-discoveries/tree/8e96d9adea76ec4719047f93e02568d49dcdcab6/frankl-height-six/verification/exactly-four-isolates/lean-deficit-two-no-quads).
After building the dependency modules with pinned toolchain/Mathlib,
append their object directory and Mathlib to LEAN_PATH. From this directory:

    sha256sum --check manifest-checked.sha256
    export LEAN_PATH="$PWD:$LEAN_PATH"
    lean -j1 -M2500 -DwarningAsError=true -o FranklTwoMateCollapse.olean FranklTwoMateCollapse.lean
    lean -j1 -M2500 -DwarningAsError=true -o FranklSaturatedFourTriples.olean FranklSaturatedFourTriples.lean

This is not a solution of the height-six conjecture.
