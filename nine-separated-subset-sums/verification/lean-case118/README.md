# Checked max-148, second-largest-118 integer branch

The accepted theorem `fourPoint118_no_descending_tail` excludes
second-largest **118** when the maximum is 148. It combines the exact
signed-score squared-weight lower bound **109,014** with a kernel
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
including the previous checkpoint. Then build
`NineSeparatedSubsetSums.FourPoint118CachedShard`.
`verified-modules.txt` is a direct compile order. The Python generators
are optional: their output, not the generator, is checked by Lean.
This checkpoint does not establish any case after 118.
