# Checked max-148, second-largest-120 integer branch

The accepted theorem `fourPoint120_no_descending_tail` excludes
second-largest **120** when the maximum is 148. It combines the exact
signed-score squared-weight lower bound **108,497** with a kernel
replay of the cached centered search.

The nonnegative penalty values are encoded as fixed-width digits of
single natural numbers, with zero values past their stored width.
The general packed geometry helper proves support, budget identity
and the connection to actual signed four-point charges. The finite
parity anchors and budget identities are checked with ordinary
`decide +kernel`. The final theorem uses only
`[propext, Classical.choice, Quot.sound]`, without native compiler
trust or admitted proofs. All required compiled logs are retained.

Add these data and source files to the existing Lean 4.36.0 project
including the previous checkpoint. The 120 package also requires the
eight-point helpers and concrete 120/119 theorem from the [separate
checked pilot](../lean-eightpoint-120-119); it includes a new checked 120/118 eight-point branch.
Then build
`NineSeparatedSubsetSums.FourPoint120CachedShard`.
`verified-modules.txt` is a direct compile order. The Python generators
are optional: their output, not the generator, is checked by Lean.
This checkpoint does not establish any case after 120.
