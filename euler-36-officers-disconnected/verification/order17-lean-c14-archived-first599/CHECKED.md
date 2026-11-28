# C14 exact full raw row 11641 and contiguous archive through 599
Strict ordinary Lean 4.36, one worker, -M2450, warnings as errors,
overlay TMPDIR, unchanged 98s global/17s per-leaf bounds. New bounded
carry attempt passed in 61.28s wall (50.63 user/7.81 sys). Precisely
21 prior exact source/object/log
records were validated and 19 fresh modules were compiled. Earlier
frozen sources and archive were not modified.

The kernel checks all 509 unit propagation steps, partitioned into
34 actual adjoining segment theorems, and the final conflict (510th
hint). Mathlib is shared with existing production rowAt against the
same typed GoodBelow base rowAt 9423. Exact target is raw learned clause
ID11641, dense slot 9423, 41 literals. Audited results:
  Euler.C14.PolarityDraft.slice11641 :
    ∀ base : Sat.Fmla, Slice base rowAt 9423 9424
  Euler.C14.PolarityDraft.exactArchiveThrough9424 :
    GoodBelow archivedGlobalCore rowAt 9424
Both only propext, Classical.choice, Quot.sound. All 34 segments and
the conflict/step/slice are audited independently; final conflict uses
only propext. The former accepted exact-archive bound through 598
learned clauses is an explicit verified dependency, not an assumption
in the 599-clause aggregate. Subsequent rows, terminal contradiction,
full core containment and geometry are not reached.

Portable replay: compile the exact original production index and
through9423 release packages, then replay-local.sh with the declared
Lean and colon-separated Lean/mathlib project dependency roots.
The separate static tranche and verified local receipts can be used
on the same workspace to avoid rebuilding already checked segments.
