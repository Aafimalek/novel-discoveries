# Positively essential coordinate in a fixed one-NOT context

Assume a monotone AND/OR context F(y,a,b) is evaluated with a=x0 and
b=not x0. At each target pivot y where F(y,0,1)=0 and F(y,1,0)=1,
monotonicity in b gives F(y,0,0)=0 and F(y,1,1)=1. Thus both fixed-b
cofactors are pivotal in the positive port. In particular a circuit must
use x0 directly, not merely its complement. This necessary condition
is independent of circuit depth and fan-out.

For the existing eight-vertex example, a single active positive-port
usage clause strengthens the former usage condition (“x0 or NOT x0”)
without discarding a correct circuit. This is not a gate lower bound or
an official upstream contribution. The two equalities could optionally
be imposed in extra counterfactual test columns; that adds variables and
should be benchmarked rather than assumed advantageous.

Both generic statements in PositiveInputPivots.lean passed Lean 4.36.0
with warnings as errors and no axioms. The static replay enumerates the
13 positively pivotal settings, changes only clause 27866 of the pinned
fixed-x0 instance (56 to 28 literals), and independently validates the
existing 16-gate positive control on every input. It launches no solver;
the 14-gate question remains open for this instance.

Replay the static encoding with `python3 check.py`; rebuild the two
lemmas with Lean 4.36.0 using `lean -DwarningAsError=true PositiveInputPivots.lean`.
