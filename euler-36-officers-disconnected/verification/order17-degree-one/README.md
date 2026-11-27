# Size-17 Euler arrangements: degree-one audit

This package excludes every 17-placement maximal partial arrangement of
Euler's 36 officers that contains a frequency-one label. The earlier
result puts the unrestricted minimum at **17 or 18**. The remaining
size-17 question concerns arrangements whose minimum label frequency is 2.

The checked case families are recorded in `manifest.json`:

- Anchor maximum partner degree 3, 4, 5, or 6: all excluded.
- Anchor partner degrees 1, 2, 2: both normalized cases excluded.
- Anchor partner degrees 1, 1, 2: all 14 normalized cases excluded.
- Anchor partner degrees 2, 2, 2: the count profiles 110, 111, 210, and
  211 are excluded, along with all three normalized diagrams for the
  all-high count profile 000.

The partner degrees are the frequencies of the other three labels in
the word belonging to a degree-one label. Three partner degrees all 1
would make an isolated word, contradicted by the previous disconnected
lower bound. The exhaustive mathematical splits and the extra constraints
are justified in [the reduction](REDUCTION.md).

## Reproduce

Python 3.10+, [Kissat 4.0.4](https://github.com/arminbiere/kissat/tree/rel-4.0.4),
and the [pinned DRAT-trim](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985) are sufficient.

```sh
python -m pip install python-sat==1.8.dev24
python generate.py 112-3-5-3 /tmp/case.cnf
python verify.py --case 112-3-5-3 --solve /path/to/kissat --checker /path/to/drat-trim
```

Omit `--case` to run every manifest case. Regeneration checks the exact
DIMACS SHA-256. The audit records the SHA-256, encoding, and byte length
of each checked proof and the hash of its retained replay output. The
proof binaries are not in this package. To replay obtained original
proofs rather than regenerate them, use `--proof-dir /directory` with
canonical manifest IDs as proof filenames and the encoding's
`.drat` or `.drat.gz` suffix. A regenerated proof need not have the
same hash as the recorded proof, but it must independently replay.

The SAT proofs have not been replayed in Lean.
