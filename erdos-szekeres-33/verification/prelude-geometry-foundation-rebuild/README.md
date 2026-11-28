# Seven-source Lean rebuild of the ES33 geometry foundation

A fresh source root with the literal planar Prelude successfully
rebuilds the six downstream modules QuadrupleReduction,
TriangleOrientation, QuadrupleParity, OrientationClauses,
Signotope, and FullReduction. The six module builds and their
recorded audits passed on Lean 4.36.0 / Mathlib
fc4f59e577feb1a4956671bc04ac18aaaf8cd842 with one worker.
The exact four-point parity table is axiom-free; the other
printed endpoints use only propext, Classical.choice, Quot.sound.

The exported Plane and orient definitions are unchanged. The
first two legacy sources only move those definitions to the
Prelude and replace a broad tactic import with targeted imports.
The following four sources are unchanged. The archive includes
source and exact compiler and axiom receipts for the two waves.
No old ES33 objects were used in those builds.

This is a rebuild of foundations, not a solution to the
33-point problem. The later anchored-target geometry,
concrete reflection and lex combination, numbered clause
transport and target refutation are distinct pending steps.

For replay, use a fresh directory with the pinned Mathlib build
on LEAN_PATH and no prior ES33 object directory on it. Run
`bash replay.sh`. No solver is called.
