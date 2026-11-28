# Novel discoveries

Results on open problems in verifiable fields, mostly mathematics. Each result comes with something you can run to check it, such as a Lean proof or an exact computation.

Each folder holds one result, its research note and its checks. See [Publications and citations](PUBLICATIONS.md) for released papers and verified DOIs.

| Result | Field | Checks |
| --- | --- | --- |
| [Fink's conjecture on recursive divisors](fink-conjecture-on-recursive-divisors/) | Number theory | Lean 4 proof, exact check through $10^6$ |
| [Erdős Problems #385 and #430: settled for almost all $n$ (still open for all $n$)](erdos-385-430/) | Number theory | Lean 4 reductions and density theorems; the $\sqrt n$ result checked in Lean from three classical hypotheses; exact computation |
| [The first sizes above the Latin-square bound](orthogonal-latin-square-gap/) | Combinatorics | Lean 4 gap theorem, written classification, exhaustive checks of examples |
| [Euler's 36 officers and small maximal arrangements](euler-36-officers-disconnected/) | Combinatorics | [Citable preprint](https://doi.org/10.5281/zenodo.24624423); independently replayed SAT lower bound and Lean 4 upper witness |
| [Nine separated subset sums: lower bound of 149](nine-separated-subset-sums/) | Additive combinatorics | Written proof and exact checks of the numerical inputs within the argument |

Working notes: [width-three posets](width-three-posets/), [Frankl at height six](frankl-height-six/), and [additional research targets](research-roadmap.md).

The work here is AI-assisted. Each folder says what was used and what the checks cover.

Found a mistake or an earlier proof? Please open an issue.

## License

Code and Lean files are under the [MIT License](LICENSE). The research notes are under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
