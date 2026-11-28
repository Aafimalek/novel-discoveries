# Lean excludes exactly four isolates in the all-ordinary-pair case

The standalone endpoint is
`FranklForcingFiber.exact_four_allPair_not_multiple_sources`.
For an actual finite family with `NoStrictMajority` and
`WeakMinimalGround`, exactly four isolated points, at least two
sources, and `AllOrdinaryStarPairs`, it proves False. The last
hypothesis says the omitted-star blocks of the selected pairs
have size two. The cases of two, three, and at least four sources
are all covered. The one-source case is a separate checked proof.

Lean 4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842
checked ten new modules. All twenty-one printed audits use only
propext, Classical.choice and Quot.sound. The archive includes the
local sources in import order. Extract and run
`MATHLIB_ROOT=/path/to/pinned/mathlib4 LEAN_BIN=/path/to/lean bash rebuild.sh`.
The evidence here checked the ten new modules against pinned
built prerequisites; the entire portable source order was not
separately rebuilt in this release.

The higher-deficit block designs are not covered by this theorem.
It is not a Lean proof of the full five-isolate result or Frankl's
conjecture at height six.
