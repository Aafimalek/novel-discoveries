# Nine separated subset sums

**Current bounds: 149 to 161.** The [written 149 lower-bound paper and PDF](https://github.com/Aafimalek/novel-discoveries/tree/main/nine-separated-subset-sums/paper) use an exhaustive exact integer search after a reduction from real weights. Neither this branch nor the paper determines the exact optimum.

- Lean checks the reduction to the integer search, the previously published coverage through second-largest integer weight 113, and the new exact cases [114](verification/lean-case114), [115](verification/lean-case115), [116](verification/lean-case116), [117](verification/lean-case117), [118](verification/lean-case118), [119](verification/lean-case119), [120](verification/lean-case120), [121](verification/lean-case121), [122](verification/lean-case122), and [123](verification/lean-case123). Their replay instructions document the cached search and the packed penalty certificates. Integer cases 124 through 147 are still required for the complete Lean proof of 149. A [kernel-checked composition theorem](verification/lean-real-bridge) now connects those actual tail exclusions to the real claim.
- The checked cases use plain kernel computation and standard axioms, no native-decision axiom.
- [Earlier exact constant and upper-example checks](verification/check.mjs).

Aafi Khan Malek, independent researcher, selected and directed the project. ChatGPT assisted with research, proof development, writing, and verification. Codex was not used.

An [eight-point pilot](verification/lean-eightpoint-120-119) excludes the exact top triple `148,120,119` in Lean. Other third weights for second weight 120 are not covered by that pilot. [LocalChamber161](lean/NineSeparatedSubsetSums/LocalChamber161.lean) certifies 161 for the classical construction's fixed subset-sum order, not for general real weights.
