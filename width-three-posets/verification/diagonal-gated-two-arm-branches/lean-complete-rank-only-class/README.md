# Lean-checked balanced comparison for the rank-only diagonal-gated class

The audited endpoint is
**WidthThree.Diagonal.Labels.balanced_of_diagonal_gates**. Take a finite
poset, an incomparable good pair a,b such that every strict predecessor
of a is below b, and an exactly labeled exclusive branch
S = {b} union (strict upset of b minus strict upset of a). S is the
ordinal sum of a chain prefix of length h >= 2 starting at b, followed
by two chains X,Y (either can be empty). Require x_i < y_(i+d) and
y_j < x_(j+e) wherever those finite endpoints exist, with
max(d,e)+2 <= 2*h. Other cross relations are permitted. If the number
of rankings with a<b is at most half the ranking count, the theorem
provides a label z in S, distinct from a, with

    count(all rankings) <= 3 * count(a<z)
    3 * count(a<z) <= 2 * count(all rankings).

For n = |P|, rankings are the linear extensions of P, so these are
the exact 1/3 and 2/3 uniform-extension bounds. No arm length limit is
assumed. The unrestricted width-three problem and the wider offset cap
using conditional XYZ are not proved here.

The proof uses exact positions of common prefix labels, checked
single- and joint-anchor rank pooling, and bin monotonicity from the
checked branch swap. In the absence of balance, all prefix comparisons
are low; a least high on a rail has a low prefix. The all-low case is
excluded by covering rankings with two comparisons and a final cut.
One-high cases use a deliberately absent finite gate endpoint and the
imbalance anchor bound. The verified head-count contradiction covers
the two-high case. No factorization of ranking and cut is assumed.

## Strict verification

Lean 4.36.0 (commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9) and
Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842 compiled the theorem
and the independent fresh typed audit, each with one worker, -M2450,
and -DwarningAsError=true. Both exited cleanly. The audit reports only
propext, Classical.choice, and Quot.sound for the endpoint, exact
prefix position, and final-cut comparison. The source filename
DiagonalBalancedDraft.lean is its verified module name.

This source-only delta depends on the checked DiagonalAnchorsDraft
module (strict anchor package) and its already verified prerequisites.
With audited objects and pinned Mathlib on LEAN_PATH and the pinned
executable in LEAN_BIN, run ./replay.sh from a writable overlay copy.
Recorded logs and original object digests are under logs/; objects
are not shipped. The tiny arithmetic diagnostic is optional and not
used by Lean.
