# Joint rank slots 50 and 64

The preceding rank-slot witness test considered each slot independently.
This extension asks whether one common weight vector can satisfy both
slot constraints, for the single central orientation `++++-+---`.
The central orientation is positive: its signed dot product is the
central gap $g=s_{257}-s_{256}$.

The forced rank starts 158 and 172 imply the relevant base-eight
positive signed values are
$\alpha_{50}=M-d_{50}$, $\alpha_{64}=M-d_{64}$.
Their difference is not an independent variable:
$$
  \alpha_{50}-\alpha_{64}=d_{64}-d_{50}=2(s_{207}-s_{193}).
$$
The last equality is complement symmetry; indeed
$d_q=(\sum_i x_i)-2s_{257-q}$. The 14 gaps with indices
193 through 206 have total excess at most
$(1+\delta)/2$, where $M=149+\delta$, by the two forced edge windows.
Thus the following two extra affine rows are valid:
$$
  28 \le \alpha_{50}-\alpha_{64} \le 29+\delta=M-120.
$$

For each slot use its exact individual certificate to exclude already
disproved oriented forms. There are 42 remaining at slot 50 and 56 at
slot 64. Among all 2,352 cross-slot choices, the joint rank-slot LP
and the two extra affine rows above exclude **896** by exact rational
certificates. The remaining **1,456** are not excluded by this test;
no feasibility, numeric optimum or whole-orientation exclusion is claimed.
Of the 896 exact certificates, 11 need one of the original strict
inequalities $M<150$ or $g<2$. No other root or rank slots were
tested in this joint pilot.

## Replay

```sh
sha256sum --strict -c PAIRED_SHA256SUMS
python3 rank_slot_pair.py ++++-+--- --verify-only
```

Replay first verifies the single-slot certificates using the standard
library, then verifies each joint certificate. No SciPy is required
for replay. The input slot scopes and signed-form convention match
the independent single-slot packet; here the variables on both sides
of a pair are exactly the same nine weights.
