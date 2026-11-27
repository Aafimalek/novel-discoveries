# Shared-DAG conjunction lemma

`SharedOutputs.lean` is a Lean-checked helper for the circuit definitions in the [P vs NP proof project](https://github.com/open-goat/pequalnp-proofs). If two outputs of the same ordered monotone gate list accept every positive example and never both accept a negative example, one added AND gate computes a separator. The result proves the new size exactly and preserves fan-in at most two.

Checked on Lean 4.36 and the upstream pinned Mathlib at upstream revision `44678d135906cbc2060a55ec227b229b6dadd38f`. Both main declarations use only `propext`, `Classical.choice`, and `Quot.sound`. For reproduction, place the file in the upstream `lean/` directory after building its definitions and run `lake env lean SharedOutputs.lean` there.

This is support work for desk gap L-meta-17744. It does not prove that gap's numeric lower bound, has not been submitted upstream as a gap solution, and does not resolve P versus NP.

[`NormalizeGap17744.lean`](NormalizeGap17744.lean) checks equivalence between the exact desk statement and the single flag (point 0, line 0). The symmetry transports the circuit gates and outputs, both accepted quadrangle sets, their disjointness and nonemptiness, and gate count. All audits use standard Lean axioms only. The 56-gate lower bound remains unproved for the normalized case, so this is not submitted as a full gap solution. Reproduce with the same upstream revision, after placing the file under `lean/`.
