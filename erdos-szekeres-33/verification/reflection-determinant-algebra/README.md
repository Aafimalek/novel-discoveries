# Staged ES33 reflection checks (Lean 4.36.0)

The verified stage is in checked/. Against the pinned built Mathlib
fc4f59e577feb1a4956671bc04ac18aaaf8cd842, with its compiled dependencies
on LEAN_PATH, recompile checked/ReflectionAlgebra.lean using one worker:
    
    lean -j 1 -M 2100 -DwarningAsError=true ReflectionAlgebra.lean

For a commutative ring R, with Point R = R × R and
orient(a,b,c) = det(b-a,c-a), its three exact signatures are:

- orient_reverse (a b c : Point R) : orient c b a = -orient a b c
- orient_mirror (a b c : Point R) :
  orient (mirror a) (mirror b) (mirror c) = -orient a b c
- orient_mirror_reverse (a b c : Point R) :
  orient (mirror c) (mirror b) (mirror a) = orient a b c

Here mirror(x,y) is (-x,y). All three audit lines use only
propext, with no sorry or native-computation axiom. The exact clean
compile took 1.206 seconds and peaked at 1,212,552 KiB RSS. This confirms
the algebra without invoking real analysis, the ES33 geometry imports,
or a normalization tactic such as ring or linarith.

The remaining modules are independent handoff sources, not claimed
checked unless moved to checked/ with a matching exit-zero receipt.
This does not prove any exact orbit-numbered target UNSAT.

The adapter importing the existing published TriangleOrientation object did
not reach an exit zero: 65.135 seconds, 1,577,940 KiB peak RSS, 7.088 seconds
user CPU, 22.096 seconds system CPU, killed at the explicit wall limit.
It emitted no theorem or elaboration diagnostics. The geometry and final
lex stages were not started. This is an import-bearing build timeout, not
a discovered mathematical error and not a verified adapter.
