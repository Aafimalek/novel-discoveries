# Checked ES33 real determinant Prelude and adapter

The two new modules were compiled in a fresh output root on Lean 4.36.0
and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The general
commutative-ring arithmetic was previously checked and its exact compiled
object reused. The Prelude contains the literal definitions moved from
the two project source modules; their names, types and bodies are
unchanged. This release contains source and receipts, not binary objects
or a replacement of the complete geometry stack.

The plain notation (e.g. mirror) below names the definitions in namespace
ES33.GeometricReflection. Variables a,b,c all have type ES33.Plane.

- project_orient_eq: ES33.orient a b c = ES33.ReflectionAlgebra.orient a b c.
- orient_mirror: ES33.orient (mirror a) (mirror b) (mirror c) = -ES33.orient a b c.
- orient_mirror_reverse: ES33.orient (mirror c) (mirror b) (mirror a) = ES33.orient a b c.

All three depend only on propext, Classical.choice and Quot.sound.
Prelude elapsed 1.712 seconds, adapter 1.313 seconds, with one Lean
worker and a highest sampled RSS of 1,726,980 KiB. See adapter.log and
verified-stage-receipts.json for exact scope and artifact fingerprints.

To reproduce in a matching compiled Mathlib environment, create a fresh
source/build root (do not include any old ES33 object directory on
LEAN_PATH), compile ReflectionAlgebra.lean and ES33/PlanarPrelude.lean,
then compile RealDeterminantAdapter.lean. Place each produced object
in the build root at the corresponding module-relative path and
include that root on LEAN_PATH. This checks the determinant bridge;
none of the thirteen legacy downstream modules, convex/cup
preservation, the concrete lex-leader instance, nor target UNSAT was
checked in this run.
