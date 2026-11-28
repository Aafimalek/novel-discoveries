# A six-color certificate for the rotation field

The [written transfer](field-transfer.md) proves a six-color upper
bound for the complex unit-distance graph on Q(√−3, √33, √−7).
The finite residue certificate on 289 vertices is fully checked in
ordinary Lean 4.36.0. Exactly 2,601 unordered edges are independently
checked by Python. The Hensel/17-adic transfer itself is not in Lean.
This is not a six-color lower bound for the field or a new bound for
the unrestricted plane.

The exact Lean endpoint `proper_norm_one_difference` says for any
two pairs of Fin 17 coordinates, a modular norm-one difference
forces different Fin 6 colors from the supplied table. Only
`propext` and `Quot.sound` occur. The packed table decodes to
[the same digits](colors.txt) used by the independent check.
The strict build log, original-process result and source hash
records are included; the compiled object is not bundled.

Recheck from a writable directory using pinned Lean 4.36.0:

    sha256sum --check SHA256SUMS
    python3 replay_f17.py
    mkdir -p overlay-tmp
    TMPDIR="$PWD/overlay-tmp" lean -j1 -M1100 -DwarningAsError=true -o F17ResidueTable.olean F17ResidueTable.lean
