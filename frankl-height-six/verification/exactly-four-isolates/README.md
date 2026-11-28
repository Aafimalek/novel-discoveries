# Exactly four isolates: at most one forcing center

The [written proof](theorem-note.md) rules out every multi-center case for
a ground-minimal weak height-six family with exactly four isolates.
The zero-center case is impossible as well. For one center, exact trace
enumeration eliminates 105 of 106 candidates. The remaining candidate
has all 16 traces of the isolates in the source-containing fiber
except one singleton. This is a necessary model, not a constructed
counterexample. The proof does not resolve it or exclude five or more isolates.

[Paper PDF](paper/exactly-four-isolates.pdf) · [TeX](paper/exactly-four-isolates.tex)

The finite replay needs only Python and no external solver:

```sh
python3 traces.py
sha256sum --strict -c SHA256SUMS
```

The multiple-source argument uses existing Lean-checked components
and the cited 12-element theorem, but its new mathematical composition
and the trace exclusion are not checked end to end in Lean.
