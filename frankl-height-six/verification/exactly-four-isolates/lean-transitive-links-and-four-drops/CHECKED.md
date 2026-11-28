# Checked actual transitive link quotients

The four named modules checked using direct pinned Lean 4.36,
warning as error, one worker, 2500 MB, and overlay temporary storage.
The replay checks new modules against previously checked imports.

The concrete conditional endpoint
`FranklForcingFiber.exact_four_deficit_two_ordinary_pair_not_four_linked_drops`
assumes an actual weak minimal NoStrictMajority family with four isolates,
source degrees at least k−3, two distinct exact-deficit-two anchors whose
omitted block is just those anchors, and at least four dropped outsiders,
each linked by a path to a retained outsider. These conditions imply
False. This does not supply the paths or prove a four-cycle
classification, the broader exact-four result, or the unrestricted
height-six conjecture.

The reusable endpoint `transitiveDeletion_of_rooted_link_regions`
turns a finite disjoint collection of linked regions with selected
roots into exactly the sum of (region size minus one) dropped outsiders.
The geometric file also checks a true-support and isolate-deletion lift
for the quotient formed using paths instead of direct neighbors.
