# Lean-checked one-step repair for Frankl's height-six problem

Lean checks all three stages of the maximal-missing-deletion argument:
existence and union closure of the repair, preservation of height, and
the contradiction for the 15/7/at-least-8 containing-fiber profile.
The endpoint is
`FranklForcingFiber.no_containing_profile_fifteen_seven_eight`.

All eight audited theorems use only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. The endpoint takes the trace
frequencies as hypotheses. It does **not** certify the finite trace
classifier or the full [at-least-five-isolates theorem](../) end to end,
and it does not formalize the more general surplus-(d) repair.

Replay in Lean 4.36.0 with pinned Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and the compiled
`FranklForcingFiber` and `FranklLowFrequency` modules from the
[existing project](https://github.com/Aafimalek/novel-discoveries/tree/99abc567470ea8669712272bee26b25a81a0b6ee/frankl-height-six/lean).
Put these artifacts and Mathlib's dependencies on `LEAN_PATH`. Then:

```sh
sha256sum --strict -c SHA256SUMS
bash replay.sh
```

The [clean replay log](replay.log) records the actual successful build
and the exact axioms. No compiler object files are required from this
release. No Codex was used.
