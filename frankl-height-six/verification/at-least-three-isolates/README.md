# At least three isolates in the ground-minimal height-six Frankl model

**Theorem.** If a finite nonempty union-closed family of nonempty sets has no
strict chain of seven distinct members and every point occurs in at most half
of its members, and its ground size is minimal among such weak families, its
proper forcing graph has at least three isolated points.

[Paper PDF](paper/few-isolates.pdf) · [TeX](paper/few-isolates.tex)

The no-isolate case was checked earlier. The new analytic argument excludes
one and two isolates for any number of forcing stars. It replaces, rather
than relies on, the earlier finite one-isolate exclusions in
[signature-moments](../signature-moments/). Height six remains open; the theorem
does not exclude families with three or more isolated points.

The key inequality is for a finite pair design on its forcing-star centers:
if the minimum number of incident blocks is g, there are at least g(g+1)/2
blocks. The compressed pair fiber meets at most g−1 distinct signatures
outside a block through a minimum-degree center. Comparing the resulting Sauer
upper bound with the checked count from the blocks avoiding two centers gives
the contradiction. No bounded search or solver is needed.

## Lean scope

The existing verified inputs are `partition_card`, `sources_card_le_leaves`,
`starBlocks_pairDesign`, `leaf_pair_count_with_blocks`,
`compressed_pair_signatures_eq_of_blockLink`,
`pair_fiber_card_le_sauer_block_signatures`,
`unique_source_isolated_card_ge_three`, and
`isolated_nonempty_of_weakMinimalGround`. These are in the parent
[Lean sources](../../lean/) and the earlier
[signature-Sauer development](../signature-moments/). The new minimum-degree
argument and its final composition are in the written proof; this release
does not claim an end-to-end Lean theorem.
