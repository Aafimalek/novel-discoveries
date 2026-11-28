# Six all-grid additions: unique degree-one vertex with four new neighbors

**Verified.** This subcase preserves five-colorability given the earlier
five-point theorem. All 32 exact shards completed under the same
132,000 KiB virtual-memory cap. Of 872,165 raw four-rim sets, 83,818 pass
the relaxed rim-degree check. There are exactly 3,833,277, 145,271, and
33,796 eligible six-point configurations with zero, one, and two missed
contacts, respectively. The verified palette bank covers every one of
the 4,012,344 configurations, with zero residuals. No SAT solver was
used. Other six-point cases are not claimed by this package.

[Paper (PDF)](paper/g449-six-one-nonuniversal.pdf) · [TeX](paper/g449-six-one-nonuniversal.tex) · [Complete replay archive](one-nonuniversal-replay.tar.gz)

A fresh run regenerated all inputs, then matched all 32 checked shard
logs and empty residual files. Together with the earlier
[off-grid](../six-off-grid-extensions/),
[degree-zero](../six-grid-universal-zero-hub/),
[multiple degree-one](../six-grid-multiple-degree-one/), and
[one-neighbor universal](../six-grid-one-universal-hub/) proofs, this
leaves only six-grid-point additions where every new point has at least
two original neighbors.

Assume every five-point extension of the pinned G449 graph is
five-colorable. For an added point $v$, let $b(v)$ be its number of
original neighbors and $d_H(v)$ its degree among six additions.
A failing configuration has
[
\delta_{\rm add}=\min_v\left(b(v)+d_H(v)\right)\ge5,
]
by deletion and greedy extension. Here the sole $b=1$ point $h$ has
exactly four new neighbors $R$, and misses a fifth point $w$.
A $b=0$ point would have to be universal and share at least three
neighbors with $h$, so every point other than $h$ has $b\ge2$.

## Complete finite search

1. Regenerate the 7,056 grid points with $b\ge2$ and 222,264 with $b=1$
   from the exact signed step catalogue and pinned base coordinates.
   For every possible rim point translate by all 546 steps. Partition
   the 3,852,576 generated incidences by the exact hub key and keep
   hubs with $b=1$, storing the index of that original neighbor.
   The prior independently checked incidence histogram gives 109,683
   retained incidences, 30,233 hubs with any available rim points,
   12,558 with at least four, and 872,165 raw four-rim choices.
2. For each hub, the rim sits on the unit circle and exact rim
   adjacency follows $\pm60^\circ$ orbits, so components have
   at most six vertices. A selected rim point requires
   $b(v)+d_R(v)\ge3$, because its hub edge and at most one
   edge to $w$ contribute at most two. Iteratively peel vertices
   that cannot meet this even with all remaining rim neighbors.
   Combine eligible subsets from distinct components in fixed
   component order to obtain each four-rim set once.
3. Define the required rim contacts to be those with
   $b(v)+d_R(v)=3$. The missed point must hit all such contacts.
   Because $h,w$ are distinct and share at most two unit neighbors,
   $t=|N(w)\cap R|$ is 0, 1, or 2. More than two required contacts
   renders this rim set impossible. A completion must satisfy
   $b(w)\ge5-t$. Check the three cases separately:
   - **Zero.** No required contacts, $b(w)\ge5$, and $w$ is not
     adjacent to any rim or to $h$, or equal to any selected point.
     Static bitsets range over the 574 $b\ge5$ points. Subtract the
     hub neighbors and the rim points and their neighbors; this
     counts every valid isolated completion exactly once. For a
     given proper base palette, the bitset of isolated sites with
     a nonempty list is precomputed. The union of those bitsets
     over palettes that color the hub plus its four rims gives
     exactly the covered isolated completions.
   - **One or two.** Enumerate the union of neighbor sets of the
     four rims restricted to $b\ge3$. For a candidate $w$, compute
     the complete four-bit contact mask by exact step lookup;
     visit it only from the least contacted rim index. Reject
     if it sees $h$, equals a selected point, misses a required
     contact, or has $b(w)+t<5$. This produces each valid
     one-contact or two-contact completion exactly once.
4. For every coloring palette, remove the color of the hub's
   sole original neighbor from the hub list. A trial hub color
   is then forbidden at all four rim vertices but **not** at
   $w$. The exact finite list search checks all rim edges,
   all edges to $w$, and all lists derived from the original
   neighbors. An optional shortcut rejects a palette if it
   cannot already color the hub and its four rims. Residuals
   are bank gaps, not witnesses of six-chromaticity.

Uniqueness of the hub, of the four-rim set, and of the missed
vertex makes this duplicate-free globally. The only other multiplicity
in generation (multiple contacts in the attached branch) is removed
by the least-contact rule. Each whole hub is in a single shard.

## Clean replay

Use Python 3.10+, NumPy, GNU C++20, and the existing exact helpers
`audit_layers.py` and `two_point_replay.py` on `PYTHONPATH`:

```sh
PYTHONPATH=PATH_TO_EXACT_HELPERS bash ./replay.sh \
  PINNED_G449_INPUT_DIR denominator-seven-directions.tsv \
  extension-witnesses.json triple-residual-witness.json \
  four-witness.json five-witness.json FRESH_RUN_DIR
```

Each compile or shard invocation is separately timeout-bound; the
full serial run may exceed 30 seconds. Use the recorded `-O0 -g0`
compiler options to stay within the memory guard. The separately
checked full shard logs and empty residual files are in `checked/`:

```sh
sha256sum -c CHECKED.sha256
python3 collect.py checked 32 --expect-closed
```

The SHA-256 pins are identical to the prior hub replays. Take
the [original G449 input files](https://github.com/bprzybocki/G449/tree/125bfda97ed1d336f84694de04dedcfb349c5164),
the helpers, signed directions and first two witnesses from this
catalogue's parent directory, and the
[four-point](../four-five-point-extensions/four-witness.json) and
[five-point](../five-point-extensions/five-witness.json) witnesses from
their proof packages. The runner applies a hard
132,000 KiB virtual-memory cap and 25-second per-command timeouts,
stops at the first unresolved bank residual, and accepts only a
complete receipt. The sharded kernel has explicit caps on
incidences, rim visits, attached completions, and emitted residuals;
it cannot emit a completion receipt after exceeding a cap.
