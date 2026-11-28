# Checked no-quad branch

`FranklForcingFiber.exact_four_deficit_le_two_no_quads` proves that
a weak minimal NoStrictMajority family with exactly four isolated
points and source degree at least k−3 everywhere cannot have a
four-source omitted-star block.

The checked outside-deficit-two contradiction forces any quad to be
unique and leaves only disjoint exterior triple blocks. If there is a
triple, the linked mate groups supply three drops at a quad/triple
anchor pair, contradicting its capacity. With no triples, the prior
sole-quad exclusion applies.

This does not exclude the triples-only case or prove the full
exact-four result. The new source replays against checked local
prerequisites using pinned Lean 4.36, one worker, 2500 MB,
warnings-as-errors and overlay temporary storage.
