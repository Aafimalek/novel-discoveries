# Two exact negative checks for distance-two gadgets on G449

[Paper (PDF)](mirror-terminal-equality.pdf) · [TeX](mirror-terminal-equality.tex)
· [Exact replay archive](mirror-replay.tar.gz)

A distance-two terminal pair forced to differ in every proper five-coloring
would be useful for constructing an explicit finite six-chromatic unit-distance
graph. These checks rule out two restricted routes using the fixed G449:

- Every terminal pair of the form ((x,2y-x)), for an original unit edge
  (x	o y), can share a color. This remains true after optionally adding
  any one distinct extra point in the verified denominator-seven grid.
  The replay independently checks 2,523,976 non-greedy cases; all have
  explicit positive equality witnesses.
- Every two distinct original vertices differ in at least one of the 61
  verified proper five-colorings. Thus there is no forced-equal original
  pair to use in the separate circle-intersection construction. No pair
  of original vertices is itself at distance two.

The checks use no SAT solver and are not Lean formalizations.
They make no claim about arbitrary attached terminals, off-grid
catalysts, or the chromatic number of the plane. To replay, obtain
the [six-point theorem's exact profile generator and inputs](https://github.com/Aafimalek/novel-discoveries/tree/294c4596476e933f75703479fab2ea0f87e3723e/hadwiger-nelson/verification/g449/prime-seven-catalogue/six-point-extension-theorem).
Unpack this archive and follow the `README.md` in each of
`replay/census`, `replay/reflection`, `replay/two`, and
`replay/forced-equality`. The two-addition and differing-color
checks were independently replayed.
