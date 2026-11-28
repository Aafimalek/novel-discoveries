# At least four isolates in the height-six Frankl model

**Theorem.** The proper forcing graph of a ground-minimal weak height-six
family has at least four isolated points. A weak family here is finite,
nonempty, union-closed, has no empty member or strict chain of seven members,
and has each point in at most half its members.

[Paper PDF](paper/three-isolates.pdf) · [TeX](paper/three-isolates.tex)

The [previous argument](../at-least-three-isolates/) excludes zero, one
and two isolates. This revision excludes exactly three for arbitrarily
many forcing stars, including the single-center case:

- With two or more centers, the incidence deficit and the agreement of
  two link partitions force every block of the omitted-star design to be
  a pair. A rank-two intersection-family bound forces relative
  co-singletons in every leaf-pair avoidance fiber. Union closure makes
  enough new witnesses containing both leaves to exceed the checked
  avoidance upper bound.
- With one center, there are seven containing traces. Comparing the
  number of avoiding members with both of two specified isolates to
  the number with neither contradicts the height-two bound for the
  isolate-free subfamily.
- With no center, there are three ground points and no singleton
  members, contradicting the frequency bound by total occurrences.

No finite search or unproved computational result is used. The
combinatorial composition and the theorem are **not yet formalized end
to end**. Arithmetic sublemmas for the deficit and the fiber slack are
separately verified in [Lean](lean/ThreeIsolatesArithmetic.lean).
To replay those under Lean 4.36.0, no Mathlib required:

```sh
sha256sum --strict -c SHA256SUMS
lean -j 1 -M 650 lean/ThreeIsolatesArithmetic.lean
```

The height-six problem remains open: this theorem does not exclude
families with four or more isolates.
