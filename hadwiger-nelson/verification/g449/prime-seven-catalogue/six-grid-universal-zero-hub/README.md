# Six-point all-grid degree-zero hub: exact replay

**Result.** Given the [earlier arbitrary five-point theorem](../five-point-extensions/), adding six
grid points to G449 preserves five-colorability if at least one of the
six has no original neighbor. All 32 bounded replay shards completed
with no residual. This does not address all six-point extensions, nor
does it improve a bound for the entire plane.

Of 3,852,576 generated rim-to-hub incidences, 3,656,583 remain after
excluding original points and their neighbors. They land on 3,384,633
possible hubs, 15,638 of which have at least five available rim points.
The unpruned sum of five-element rim choices is 715,925. The minimum
total degree test leaves 4,578 configurations, all colorable by an
existing palette. Although 38 palettes were verified, only the
first 25 were needed; no new coloring witness or SAT solver was used.
The checked per-shard receipts are in `receipts.txt`.

[Paper (PDF)](paper/g449-six-universal-hub.pdf) · [TeX](paper/g449-six-universal-hub.tex) · [Replay archive](zero-hub-replay.tar.gz)

A fresh independent run regenerated the exact input and matched every one of the 32 shard receipts.

## Scope and completeness

Assume the earlier arbitrary five-point extension theorem. For a
six-point extension write $b(v)$ for degree in the original 449 points
and $d_H(v)$ for degree among the six new points. A counterexample
satisfies $\delta_{\rm add}:=\min_v (b(v)+d_H(v))\ge5$, by deleting
and greedily restoring any vertex with at most four total neighbors.

If $b(x)=0$, then $d_H(x)=5$: $x$ is adjacent to all five rim points.
No other new point can have $b\le1$: two distinct points have at most
two common unit neighbors, so every other point has at most two rim
neighbors on the unit circle around $x$, hence at most three new
neighbors including $x$. The other five therefore each have $b\ge2$.
Their candidate set is the 7,056 outside grid points having at least
two original neighbors. The 546 signed exact directions generate all
3,852,576 candidate rim-to-hub incidences. Exclude original points and
points with any original neighbor. Shards partition the remaining
candidate hubs by a fixed hash of their exact coefficient key; **all
incidences for a given hub go to the same shard**.

For each candidate hub, use exact displacement membership for all
rim adjacency. On a unit circle, unit edges move by $\pm60^\circ$,
so the full available unit-circle graph has components of at most
six vertices and maximum degree two. Selected sets of five are
disjoint paths. A selected rim $v$ must have $b(v)+d_{\rm rim}(v)\ge4$.
Iteratively discard a rim site that cannot meet that inequality
even with every remaining possible neighbor; by induction, this
does not discard a rim from an eligible set. Within each component
enumerate all nonempty subsets of size at most five that meet the
inequality for every selected rim. Then combine subsets from disjoint
components in increasing component order to size five, skipping
components as needed. This enumerates all eligible rim configurations
exactly once. The program also records the unpruned sum of
$\binom{|\mathrm{available\ rim}|}{5}$ over hubs.

For every bank coloring, derive each rim color list by removing the
colors at its actual base neighbors. Try all five colors at the
degree-zero hub and remove the chosen color from each rim list.
An exact finite list solver propagates assignments and tries all
remaining colors if necessary. Any positive result is a proper
five-coloring of the induced extension. A configuration not covered
by this bank is merely a residual, not a proof of six-chromaticity.

## Reproduce

Use Python 3.10+ with assertions enabled, NumPy, and GNU C++20. Keep
`audit_layers.py` and `two_point_replay.py` on `PYTHONPATH`. As with
the earlier checks, the completeness of the grid step catalogue uses
the preceding cyclotomic pole-classification proof.

Portable input hashes are in `INPUTS.sha256`, and the 32 full
verified shard logs plus empty residual files are in `checked/`
(verifiable with `sha256sum -c CHECKED.sha256`). Inputs are not redistributed. Take the two [pinned upstream G449 files](https://github.com/bprzybocki/G449/tree/125bfda97ed1d336f84694de04dedcfb349c5164).
The parent catalogue directory contains both exact helper scripts, the
signed directions, and the single- and triple-point palette inputs.
The [four-point](../four-five-point-extensions/four-witness.json) and
[five-point](../five-point-extensions/five-witness.json) witnesses are
in their corresponding proof packages.

From this package:

```sh
sha256sum -c CHECKED.sha256
python3 collect.py checked 32 --expect-closed
PYTHONPATH=PATH_TO_EXACT_HELPERS timeout 100s bash ./replay.sh \
  PINNED_G449_INPUT_DIR denominator-seven-directions.tsv \
  extension-witnesses.json triple-residual-witness.json \
  four-witness.json five-witness.json FRESH_RUN_DIR
```

The clean runner pins every input and the generated `work.txt` both
before and after the shards. It uses a 132,000 KiB virtual-memory
limit and individual 25-second timeouts, with a low-memory GCC
garbage-collection setting for compilation. The previously recorded
`checked/input.sha256` verifies the generated file given the same inputs.


`prepare.py` first verifies the hashes of the two pinned input files,
checks the exact signed catalogue, and verifies all 2,198 induced
base edges and all supplied proper base colorings. The C++ pass reads
all 12 coefficients of every vertex and step, checks key round trips,
exact sign symmetry, coefficient bounds, properness against all
original edges, and independently regenerates the original neighbor
map from directions. The base-256 key is an exact linear packing, not
a truncated fingerprint: in each equality comparison the differences
between corresponding coefficients have absolute value less than 256
(by the asserted range bounds), so equality of packed keys proves
coefficientwise equality by reducing mod 256 and inducting. Hash
collisions cannot merge stored keys. The only sharded index has a hard
300,000-record cap (32 bytes per record on the tested compiler target).
The bank is capped at 64 proper colorings; the other fixed data
structures involve at most 245,154 original incidences and 229,769
excluded points. An eligible-shard visit or residual output cap is
also enforced. Increase the shard count or budget if needed; no
incomplete run can emit a completion line or be accepted by collection.
