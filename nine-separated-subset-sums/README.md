# Nine separated subset sums

**Current bounds: 149 to 161.** The [written 149 lower-bound paper and PDF](https://github.com/Aafimalek/novel-discoveries/tree/main/nine-separated-subset-sums/paper) use an exhaustive exact integer search after a reduction from real weights. Neither this branch nor the paper determines the exact optimum.

- Lean checks the reduction to the integer search, the previously published coverage through second-largest integer weight 113, and the [new case 114](lean/NineSeparatedSubsetSums/FourPoint114CachedShard.lean). The [replay instructions and audit](verification/lean-case114) explain the new cached search. Integer cases 115 through 147 are still required for the complete Lean proof of 149.
- The [case 114 proof](lean/NineSeparatedSubsetSums/FourPoint114CachedShard.lean) uses plain kernel computation and standard axioms, no native-decision axiom.
- [Earlier exact constant and upper-example checks](verification/check.mjs).

Aafi Khan Malek, independent researcher, selected and directed the project. ChatGPT assisted with research, proof development, writing, and verification. Codex was not used.
