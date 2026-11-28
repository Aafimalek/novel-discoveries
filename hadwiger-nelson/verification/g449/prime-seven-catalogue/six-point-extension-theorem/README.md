# Adding any six points to G449 preserves five-colorability

[Paper (PDF)](g449-six-point-extension.pdf) · [TeX source](g449-six-point-extension.tex)
· [Exact replay archive](g449-six-point-replay.tar.gz)

**Theorem:** Adding up to six distinct points anywhere in the plane to
the fixed Heule–Przybocki 449-point unit-distance graph, with all new
unit edges, still permits a five-coloring.

The earlier exact results cover
[connected additions](https://github.com/Aafimalek/novel-discoveries/tree/018eda729500e0bbafca0557172bd6b0afe0b337/hadwiger-nelson/verification/g449/prime-seven-catalogue/six-grid-connected),
[off-grid additions](https://github.com/Aafimalek/novel-discoveries/tree/6376de4361b98f605326dd6275fa5f9e8b5dd3fb/hadwiger-nelson/verification/g449/prime-seven-catalogue/six-off-grid-extensions),
and additions having [low original degree](https://github.com/Aafimalek/novel-discoveries/tree/f7be4c235d3d6bc073058db7fb201663ed7955e7/hadwiger-nelson/verification/g449/prime-seven-catalogue/six-grid-one-nonuniversal).
The new result covers all ten remaining disconnected component-size
partitions. The final two joins cover **7,251,680** and **70,668,216**
query tuples respectively, without a disjoint acceptance mask.

The final replay checks all original color vectors directly, regenerates
all 7,056 candidate sites and their edges, enumerates exact component
masks, and checks common-palette coverage. No SAT solver is required.
Unpack the archive and follow `replay/REPLAY.md` and
`replay/last-joins/README.md` for the guarded source replay. Only the
original G449 coordinate files are external, at the [pinned authors'
commit](https://github.com/bprzybocki/G449/tree/125bfda97ed1d336f84694de04dedcfb349c5164).
The independent re-generation and portable receipt audits are included.

This is an exact computational proof for this fixed graph, **not** a
Lean theorem and **not** a new bound for the whole plane. It does not
settle whether seven added points can force a sixth color.
