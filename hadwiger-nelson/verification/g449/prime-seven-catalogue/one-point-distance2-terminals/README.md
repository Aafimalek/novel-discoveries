# Every one-point distance-two terminal on G449 can share its color

[Proof (PDF)](single-terminal-equality.pdf) · [TeX](single-terminal-equality.tex)
· [Exact replay archive](single-terminal-replay.tar.gz)

For any original vertex (x) of the fixed G449 and any single added
point (z) anywhere in the plane at distance exactly two from (x),
some proper five-coloring of the full extension gives (x,z) the same
color. This rules out a one-point distance-two gadget on this base.
It is not a result for larger gadgets, a Lean theorem, or a plane
chromatic bound.

The exact grid check finds and colors all 861 true distance-two pairs
at original degree at least two. The off-grid proof uses the previously
verified two-neighbor cap and a common palette differing on both
neighbors for every one of 44,957,472 distinguished original triples.
Both computations were independently rerun with byte-identical outputs.

For a solver-free replay, unpack this release and the
[six-point theorem's archive](https://github.com/Aafimalek/novel-discoveries/tree/294c4596476e933f75703479fab2ea0f87e3723e/hadwiger-nelson/verification/g449/prime-seven-catalogue/six-point-extension-theorem).
Use the latter archive's `make_profiles.py` to rebuild the exact
coordinates and `graph61.txt`. Below, `EXT` is the path to that
archive's extracted `replay` directory, `BASE` is the pinned
G449 input folder, and `P` is its fresh profile output directory.
Relative paths `shared/`, `grid/`, and `offgrid/` are in this
release's extracted `replay` directory.

```sh
sha256sum --strict -c SHA256SUMS
export PYTHONPATH="$EXT/geometry:$PWD/shared"
CAT="$EXT/palettes/denominator-seven-directions.tsv"
PAL=shared/exact-equality-filter.json
(ulimit -v 132000; timeout 25s python3 grid/filter_grid.py "$BASE" "$CAT" "$P/coordinates.txt" "$P/graph61.txt" "$PAL" grid-new.json)
cmp grid-new.json grid/terminal-pairs.json
(ulimit -v 132000; timeout 25s python3 offgrid/filter_triples.py "$BASE" "$CAT" "$PAL" triples-new.json residuals-new.jsonl)
cmp triples-new.json offgrid/triple-report.json
cmp residuals-new.jsonl offgrid/residuals.jsonl
```
