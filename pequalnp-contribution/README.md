# Shared-DAG conjunction lemma

`SharedOutputs.lean` is a Lean-checked helper for the circuit definitions in the [P vs NP proof project](https://github.com/open-goat/pequalnp-proofs). If two outputs of the same ordered monotone gate list accept every positive example and never both accept a negative example, one added AND gate computes a separator. The result proves the new size exactly and preserves fan-in at most two.

Checked on Lean 4.36 and the upstream pinned Mathlib at upstream revision `44678d135906cbc2060a55ec227b229b6dadd38f`. Both main declarations use only `propext`, `Classical.choice`, and `Quot.sound`. For reproduction, place the file in the upstream `lean/` directory after building its definitions and run `lake env lean SharedOutputs.lean` there.

This is support work for desk gap L-meta-17744. It does not prove that gap's numeric lower bound, has not been submitted upstream as a gap solution, and does not resolve P versus NP.
