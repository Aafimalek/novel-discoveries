# Checked eight-point third-weight pilot

The Lean theorem `eightPoint120_119_no_descending_tail` excludes
one precise branch: the first three descending weights (148,120,119),
with six remaining positive integer weights and distinct positional
subset sums. It uses the independently checked lower bound
**121,795** on the squared-weight sum. This checkpoint does not
exclude any other choice of third-largest weight for second-largest
120.

The certified per-parity penalties are represented as fixed-width
digits of one natural number in each table. Each block charge and
budget is checked by the kernel. `EightPointPacking` extends the
finite window and transfers the eight-point moment bound to the
actual 512 distinct signed scores; `CachedFixedThird` combines it
with a checked false search result. The final theorem uses only
`[propext, Classical.choice, Quot.sound]`; the search Boolean uses
only `[propext]`. There is no `native_decide` or `sorry`.

Build `NineSeparatedSubsetSums.EightPoint120_119Shard` in the
existing Lean 4.36.0 project with the checked 116 packed geometry
helper and preceding checkpoints. `verified-modules.txt` lists
direct compile order. The bundled `eightpoint-120-119.json` records
the exact integer certificate. Optional generation:

```sh
python make-eight-packed-shards.py 120 119 eightpoint-120-119.json
```

`find-eightpoint.py` is the numerical LP finder and is not
trusted: Lean checks the resulting certificates and the exhaustive
search independently.
