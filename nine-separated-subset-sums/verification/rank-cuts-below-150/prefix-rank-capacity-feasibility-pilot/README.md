# Exact replay of one feasible outer rank-capacity model

One deterministic input, m=9 and central orientation 0, was tested.
The resulting vector satisfies all 560 integral column bounds and all
347 sparse integer rows, independently replayed in Python. This
establishes only feasibility of the outer relaxation, not any separated
nine-weight configuration. No case has been excluded and the bound is
unchanged.

Extract the archive and run, without invoking any solver:

    python3 nine149-wide-prefix-capacity-pilot/pilot.py verify
    python3 nine149-wide-prefix-capacity-milp-pilot/one.py check

Both directories have individual source and result checksums.
