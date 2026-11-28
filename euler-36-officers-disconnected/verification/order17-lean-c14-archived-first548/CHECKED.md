# C14 exact sorted archive contiguous prefix

Ordinary pinned Lean 4.36 with strict warnings checked the exact archive through slot bound 9373. This is 548 learned rows inclusive of the earlier 453, not the full 5085-row proof. The final learned raw ID is 11582. The additional 7 adjacent slices used 5441 exact hint references.

Top theorem: Euler.C14.Production.exactArchiveThrough9373, GoodBelow archivedGlobalCore rowAt 9373, using propext, Classical.choice and Quot.sound. Each new slice and the conditional balanced band aggregate use propext only. This proves neither a terminal contradiction nor any geometry link.

Dependency source packages: c14-global-first48 SHA fa85e3a37ddd08a3697f956b58f11d7b712220357e7881d8b6544dfe39c4ad3e and c14-exact-global-first72 SHA a520bd17616bbe12a25c69770903e6e3ce39e2a2ca137968afd32a839a2ddbdc. The aggregate directly imports checked exactArchiveThrough9278 from the previous recut stage. Pin ordinary Lean 4.36 and the same Mathlib dependencies. Checked order is in checked-order.txt. The separate original stage tar contains remaining source for the incremental runner; this smaller freeze includes only sources necessary to rebuild this checked prefix and its exact aggregate.
