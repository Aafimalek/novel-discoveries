# Checked ES33 clause containment and abstract reflection transport

Lean **4.36.0**, kernel-checked without placeholders or native evaluation;
this replay uses no Mathlib imports beyond the existing dependencies (the
pinned `NumberedCNF.lean` itself imports only Lean). No SAT solver was run.

- `NumberedMatches.lean` lifts UNSAT from a numbered formula whose every
  checked clause occurs in the compiled typed formula, modulo literal
  order. The containment direction is `Matches checked compiled`; adding
  unrelated clauses to the formula being checked would not be sound.
  The basic satisfaction implication uses no axioms, and the compiled
  UNSAT transport uses `propext` and `Quot.sound`.
- `ReflectionLexTransport.lean` checks abstract lexicographic symmetry
  transport, the two guard-advance clauses and the comparison clause,
  equivalence of existential guards to Boolean lex order, and omission of
  an unused final guard. Given a witness-preserving transformation which
  swaps the two bits in every orbit pair, every witness class has a
  representative satisfying the guarded leader. Only standard axioms
  listed in the logs occur.

The particular real-plane reflection and concrete 32-label orbit
numbering have not been instantiated in Lean here. The finite external
guard audit is not yet an in-kernel containment proof for the actual
32-label numbered object. Neither the strengthened nor the original
target is proved UNSAT. The general geometry conjecture remains open.

```sh
bash check.sh /path/to/lean /path/to/pinned/NumberedCNF.lean ./es33-replay
```

Use the [pinned NumberedCNF.lean source](https://github.com/Aafimalek/novel-discoveries/blob/ef469e59b905b8f7ae3d2ffcb6d3d165923dac91/erdos-szekeres-33/verification/numbered-endpoint-cnf/NumberedCNF.lean)
as the second argument. The previously
[replayed 32-label guard audit](https://github.com/Aafimalek/novel-discoveries/tree/e34e6924be9c40322019132c4613fd241ccdef13/erdos-szekeres-33/verification/exact-guarded-clause-audit)
is complementary finite evidence, not a replacement for the missing
in-kernel concrete match.
