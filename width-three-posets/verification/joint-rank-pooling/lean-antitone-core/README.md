# Lean-checked arithmetic for joint rank pooling

Lean 4.36.0, serial `-j1 -M650`, verified the four theorems in
`WidthThree.JointPool`:

* `min_add_min_le_twice`: simultaneous truncation preserves the
  two-to-two weighted capped-rank inequality.
* `cappedSum_joint`: apply that inequality to an arbitrary finite
  list of nonnegative integral cutoff weights.
* `prefixCount_eq_cappedSum`: explicitly decompose a finite
  nonincreasing list of bins into weighted prefix components.
* `prefixCount_joint`: the desired joint inequality for these
  actual finite Nat-bin prefix counts.

Only `propext` and `Quot.sound` appear in the axiom audits. There is no
Mathlib dependency, no native computation axiom, and no placeholder.
The original draft filenames/comments are retained to preserve the
exact source bytes that were checked. They do not mean the proofs
in this packet are unverified.

This packet verifies the counting arithmetic only. The comparison
between a finite poset's ranking counts and these bin lists, and the
new structural ladder and crossed-tail theorems, are not part of this
Lean check.

## Replay

From this directory run, with the pinned plain Lean executable:

    export LEAN_BIN=lean LEAN_PATH="$PWD"
    ./check.sh JointCapDraft.lean AntitonePrefixDraft.lean

The recorded run compiled the two files in order and printed their
axioms. Verify this packet with `sha256sum -c SHA256SUMS`.
