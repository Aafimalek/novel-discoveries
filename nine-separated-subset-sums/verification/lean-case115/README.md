# Checked max-148, second-largest-115 integer branch

This checkpoint adds the no-descending-tail theorem for **115** to
the prior checked range through **114**. It does not close 116–147.

The exact per-parity four-point penalties imply the square sum is
at least **109,254**. `FourPointNumeric` separates closed finite
arithmetic from the heavy Mathlib proof of the geometric principle.
The shipped arrays are checked by ordinary Lean's
`decide +kernel`, including four shorter pieces for the last
positive-center interval. The resulting
`max148_second115_fourPoint_moment_bound` applies to actual
positional subset sums.

The cached centered search under this cutoff proves
`cachedFourPoint115_false` by `decide +kernel`. Its source and the
separate `FourPoint115CachedShard` theorem combine the computed
failure with the certified moment bound to yield
`fourPoint115_no_descending_tail`.

The Boolean theorem uses only `[propext]`; the geometric and final
exclusion theorems use only `[propext, Classical.choice, Quot.sound]`.
No `native_decide` or admitted proof is used.
Build `NineSeparatedSubsetSums.FourPoint115CachedShard` after adding
these files to the existing Lean 4.36 project through the checked
114 checkpoint. `verified-modules.txt` lists direct build order.
The penalty data are supplied for provenance; the checked proof
uses the literal arrays, not Python or an LP solver.
