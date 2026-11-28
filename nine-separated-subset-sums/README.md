# Nine separated subset sums

**Current bounds: 149 to 161.** The [written 149 lower-bound paper and PDF](https://github.com/Aafimalek/novel-discoveries/tree/main/nine-separated-subset-sums/paper) use an exhaustive exact integer search after a reduction from real weights. Neither this branch nor the paper determines the exact optimum.

- Lean checks the reduction to the integer search, the previously published coverage through second-largest integer weight 113, and the new exact cases [114](verification/lean-case114), [115](verification/lean-case115), [116](verification/lean-case116), [117](verification/lean-case117), [118](verification/lean-case118), [119](verification/lean-case119), [120](verification/lean-case120), [121](verification/lean-case121), [122](verification/lean-case122), [123](verification/lean-case123), [124](verification/lean-case124), [125](verification/lean-case125), [126](verification/lean-case126), [127](verification/lean-case127), [128](verification/lean-case128), [129](verification/lean-case129), [130](verification/lean-case130), [131](verification/lean-case131), [132](verification/lean-case132), [133](verification/lean-case133), [134](verification/lean-case134), [135](verification/lean-case135), [136](verification/lean-case136), [137](verification/lean-case137), [138](verification/lean-case138), [139](verification/lean-case139), [140](verification/lean-case140), [141](verification/lean-case141), [142](verification/lean-case142), [143](verification/lean-case143), [144](verification/lean-case144), [145](verification/lean-case145), [146](verification/lean-case146), and [147](verification/lean-case147). Their replay instructions document the cached search and the packed penalty certificates. Integer cases 148 through 147 are still required for the complete Lean proof of 149. A [kernel-checked composition theorem](verification/lean-real-bridge) now connects those actual tail exclusions to the real claim.
- The checked cases use plain kernel computation and standard axioms, no native-decision axiom.
- [Earlier exact constant and upper-example checks](verification/check.mjs).

Aafi Khan Malek, independent researcher, selected and directed the project. ChatGPT assisted with research, proof development, writing, and verification. Codex was not used.

An [eight-point pilot](verification/lean-eightpoint-120-119) excludes the exact top triple `148,120,119` in Lean. Other third weights for second weight 120 are not covered by that pilot. [LocalChamber161](lean/NineSeparatedSubsetSums/LocalChamber161.lean) certifies 161 for the classical construction's fixed subset-sum order, not for general real weights.

### Combined check

The [combined Lean theorem through second-largest weight 137](verification/lean-assembly-through137) joins the real reduction and all checked integer cases through 137. It is explicitly conditional on the remaining cases 138–147.

### Searching above 149

See [rank cuts for the interval from 149 to 150](verification/rank-cuts-below-150) for the two forbidden edge bands, all sixteen forced largest-coordinate edges, a Lean-checked paired-difference lemma, and an exact count of candidate masks at the search root. The real bounds remain 149–161.
