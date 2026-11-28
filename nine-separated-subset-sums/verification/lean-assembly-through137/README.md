# Combined Lean check through second-largest weight 137

The checked theorem `NineSeparatedSubsetSums.separated_nine_at_least_149_of_cases138_to147` combines the real rounding argument with all integer exclusions through second-largest weight 137. Its **explicit remaining hypothesis** is `∀ a : ℕ, 138 ≤ a → a ≤ 147 → NoDescendingTail a`. It does not yet prove the real lower bound without that hypothesis.

There are two source stages. `GenericAssembly137.lean` proves range dispatch and its implication for real weights, taking the certificates as parameters. `LowMemoryRealAssembly137.lean` then applies the generic theorem to the existing checked certificates. `ImportOnly137.lean` is a diagnostic, not a proof step. A separate Lean invocation checks the exact resulting statement and prints its axioms.

## Replay

Use Lean 4.36.0 and the Mathlib pin `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Use the project directory with the checked `NineSeparatedSubsetSums` modules from the [real bridge](../lean-real-bridge), [cases through 122](../../README.md), and the checked shelf modules `AdaptiveShelf123` through `AdaptiveShelf137`. Place both new package modules in that **same** `NineSeparatedSubsetSums` directory, not a second namespace root earlier in the search path. Place the diagnostic and audit files in the project directory. With the usual project `LEAN_PATH`:

```sh
lean -j1 -M2450 -R . -o NineSeparatedSubsetSums/GenericAssembly137.olean NineSeparatedSubsetSums/GenericAssembly137.lean
lean -j1 -M2450 ImportOnly137.lean
lean -j1 -M2450 -R . -o NineSeparatedSubsetSums/LowMemoryRealAssembly137.olean NineSeparatedSubsetSums/LowMemoryRealAssembly137.lean
lean -j1 -M2450 AuditLowMemoryRealAssembly137.lean
```

The referenced case packages provide sources and verification logs. This combined check uses the kernel-checked modules from those previous builds. The final independent audit prints the explicit remaining hypothesis and reports only `propext`, `Classical.choice`, and `Quot.sound`. No Codex was used.
