# Connected six-point extensions of G449

[Paper (PDF)](g449-six-connected.pdf) · [TeX](g449-six-connected.tex) · [Solver-free replay archive](g449-six-connected-replay.tar.gz)

**Every connected six-point extension of this fixed G449 is five-colorable.**
Here “connected” refers to the unit-distance graph induced by the six
added points. The preceding results reduce the remaining possibilities to
six on-grid points having at least two original neighbors apiece. The
exact connected enumeration proves five-colorability of all 11,652,641
degree-eligible configurations in that branch. Disconnected extensions
in the same dense branch are not covered. The [independent cold replay](independent-cold-replay.log) regenerated the exact geometry and recomputed all 64 shards using 40 palettes, matching the original totals without reusing any coverage. The bound for the whole
plane is unchanged and this is not a Lean theorem.

Unpack the archive, then use the instructions in `replay/README.md`.
The exact G449 coordinates and base graph are at the [pinned authors'
commit](https://github.com/bprzybocki/G449/tree/125bfda97ed1d336f84694de04dedcfb349c5164).
The other inputs are in the [pinned direction-catalogue
directory](https://github.com/Aafimalek/novel-discoveries/tree/f7be4c235d3d6bc073058db7fb201663ed7955e7/hadwiger-nelson/verification/g449/prime-seven-catalogue):
use it as `PYTHONPATH` for the exact helpers; it contains the
direction, single- and triple-extension inputs, the four-point witness
under `four-five-point-extensions/`, and five-point witness under
`five-point-extensions/`. All inputs have fixed SHA-256 hashes.
