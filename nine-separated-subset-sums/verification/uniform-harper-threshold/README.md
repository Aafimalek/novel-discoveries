# Rounding at the hypercube-bandwidth threshold

[PDF proof](bandwidth-threshold-rounding.pdf) · [TeX](bandwidth-threshold-rounding.tex)

For any number of weights (nge6), write (H_n) for the bandwidth
of the (n)-cube. If a real unit-separated configuration has largest
weight below (H_n+1), rounding every weight down gives distinct
integer subset sums with largest weight (H_n). In particular the
real optimum equals (H_n) or is at least (H_n+1); it equals (H_n)
exactly when the integer optimum does.

The proof gives an explicit boundary-maximizing Harper cut and
uses its forced, overlapping saturated rank slabs to round.
It no longer needs the projected slab to contain more than half
the smaller cube. The full proof works uniformly in (n); the
small companion replay only checks the finite boundary/count examples.

- For nine weights the reduction recovers the earlier lower bound
  of 149 from the known integer optimum 161.
- For ten weights it gives a lower bound of 275 using [Dyson's reported
  exhaustive integer search](https://github.com/pwdyson/erdos_1),
  which is not rerun or formally certified here.
- For eleven weights it reduces any real example below 527 to an
  integer example of maximum 526. The integer exclusion is not proved here.

This is not an exact solution of the real minimization problem,
nor a Lean proof of the uniform statement. It shows the equivalence
of the real and integer one-step improvements; [Notik, §7, Problem 4](https://arxiv.org/abs/2611.17360)
asks for the real improvement.

Run `python3 check_thresholds.py` for a dependency-free replay in
dimensions 3 through 14. The ten-weight integer witness at 309 is
also checked as an upper bound only. This note was developed with
AI assistance.
