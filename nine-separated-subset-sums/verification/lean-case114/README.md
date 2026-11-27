# A kernel-checked max-148, second-largest-114 branch

This package gives a fully checked new integer exclusion when the
largest proposed weight is 148 and the second-largest is 114.
The prior archived Lean results cover all smaller second-largest
weights through 113. The cases 115–147 are not claimed here.

`CachedCenteredSearch.lean` retains an incrementally updated centered
signed-difference bitset and two moments, rather than rebuilding it
from the list of chosen weights at every terminal node. It proves that
any descending collision-free tail meeting the two moment cuts would
be accepted. `CachedFourPointShards.lean` gives a reusable connection
from a sound geometric moment bound and a checked Boolean to the actual
descending-tail exclusion, plus a splitter over the third-largest
weight.

For 114, the per-parity tables verify that the square sum is at least
109,216. Their finite arithmetic is checked using `decide +kernel`,
and their charge and budget calculations imply the true geometric
moment inequality. The size-114 search is `false` by
`decide +kernel`. Its checked theorem
`fourPoint114_no_descending_tail` combines these independent parts.

The search Boolean prints only `[propext]`; generic soundness and
the actual exclusion use at most `[propext, Classical.choice,
Quot.sound]`. There is no `native_decide`. The supplied JSON is
used to generate the literal Lean tables; neither Python nor an LP
optimizer is trusted in the kernel replay.

To reproduce, add the source modules to the existing Lean
4.36.0 project through the through-113 package and build
`NineSeparatedSubsetSums.FourPoint114CachedShard`. The sequence
in `verified-modules.txt` gives a direct ordinary-Lean build order.
The separate generators reproduce the tables and concrete shard:

```sh
python make-shards.py 114
python make-search.py 114
```
