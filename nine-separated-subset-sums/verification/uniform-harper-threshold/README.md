# Rounding at the hypercube-bandwidth threshold

[PDF proof](bandwidth-threshold-rounding.pdf) · [TeX](bandwidth-threshold-rounding.tex)

For every positive integer `n`, let `H_n` be the bandwidth of the
`n`-dimensional hypercube. If a positive real configuration with
unit-separated subset sums has largest weight below `H_n + 1`,
rounding every weight down gives distinct integer subset sums with
largest weight `H_n`. Thus the real optimum either equals `H_n`
or is at least `H_n + 1`, and equals `H_n` exactly when the
integer optimum does.

The written proof gives an explicit boundary-maximizing Harper cut
and uses its overlapping saturated rank intervals. It treats the two
small dimensions directly. The finite companion replay checks
boundary and counting examples, not the general proof.

- At nine weights the reduction gives 149 from the known integer
  optimum 161. The same real lower bound is independently available
  as an [end-to-end Lean theorem](../lean-real-149).
- At ten weights it gives 275 using [Dyson's reported exhaustive
  integer search](https://github.com/pwdyson/erdos_1). That integer
  search is not rerun or formally certified here.
- At eleven weights any real example below 527 would give an
  integer example with maximum 526. This note does not exclude it.

See [Notik, §7, Problem 4](https://arxiv.org/abs/2611.17360) for
the real improvement question. The exact real optima are not
determined here, and the uniform theorem is not a Lean theorem.

Run `python3 check_thresholds.py` for dependency-free checks in
dimensions 3 through 14. It also verifies the ten-weight upper
witness at 309, not the matching integer lower bound. This note
was developed with AI assistance.
