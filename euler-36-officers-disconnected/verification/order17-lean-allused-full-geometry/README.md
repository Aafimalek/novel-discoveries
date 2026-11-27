# Euler all-used order-six branch: geometric realization of the full archived CNF

The exact existing non-lex and lex clause models are joined into
`archiveAllUsedCNF`. The principal checked theorem,
`LatinGap.PairEncoding.allUsed_geometry_full_archive`, says that if an
actual linear saturated size-17 design has all degrees at least two and
uses every degree-two pair across distinct coordinate groups, then one
of the published 17 diagrams has a valuation satisfying all clauses of
its complete modeled archive.

The simultaneous lex relabeling minimizes a single natural-number
objective, encoding the row-major scores of the (0,1), (2,0), and (3,0)
incidence blocks in decreasing priority. A bad row or column comparison
allows a swap that decreases the first affected score; an unpinned
adjacent swap never changes a pinned word. Group 1 acts on columns of
the (0,1) block. Group 2 or 3 leaves all earlier blocks unchanged.
The actual relabeling preserves the exact frequency profile, central
0000 word, and every published word pin.

Replay with Lean 4.36.0 and matching Mathlib. Put the verified
`EulerAllUsedNonLexGeometry` and `EulerAllUsedLex` and their import
closures on the Lean path. Compile modules in `verified-sources.txt`
order. All new proof axioms are standard, as recorded in the logs.
`EulerLexBits` is included as an upstream local source.

Separate prefix and suffix emitted-clause audits matched all original
signed arrays exactly and independently checked original SHA-256 hashes.
`compare_complete_audit.py` confirms that the two audits cover the same
17 originals with no gap at the boundary. It does not prove a formal
DIMACS-parser theorem. This work closes the **geometry-to-CNF** step
for the all-used branch only. It establishes no additional SAT
refutation or Lean proof of the global exact minimum.

[Replay archive](euler-allused-full-geometry-replay.tar.gz) · SHA-256 `06b689acd7e47c3a3f5c341e6712f8205a997c43c66108458f53fecf4c6c9afa`. [Independent no-gap audit](independent-complete-audit.log) and fresh direct Lean replay logs are included.
