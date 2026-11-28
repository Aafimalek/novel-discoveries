# Close-triple slot grammar and verified close-only root screen

The written normalized close-triple theorem in close-triple-slot-grammar.md
gives a disjoint partition of all 256 full signed magnitudes into 64
complete trios and 64 singleton slots. In the prescribed central rank
window, all four forced sign pairs are two-plus mirrors. Between the
forced trios at ranks 52–54 and 59–61, exactly one high singleton and
a two-plus trio must occur. In particular, for the first-six total,

    S6 >= 3 X + 109,    X = x8.

This already analytically excludes the close branch of the earlier
pilot central orientation written as -----+++-. It does not exclude
that orientation's wide branch. The cone is the established close
representative (x7,x8,x9)=(X−1,X,X+1) with 148≤X<149 and the prior
unit-separated rank structure, not the wide branch or all real weights.

The LP screen reported here appends only that one affine row to the
previous close root cuts, testing the 69 as-yet-unexcluded close duties
of the 122 residual central orientations. The archived two-way-root/
documents and replays the earlier 53 close-only exclusions and no wide
closures. The canonical top-three sign cases are +++, ++-, +--, ---;
all 69 inherited duties are in these cases. The optional P/N rows in
the written note are algebraic consequences of this row and the
central equation, not independently added here. No wide duty is
tested; a new exact close exclusion cannot conclude a whole central
orientation. The one written analytic example is recorded separately
from the completed benchmark outcome (see RESULTS.md).

Do not start until authorized. Nine deterministic disjoint shards:
eight cases each except the last with five. One serial worker, stop
at a guard or solver failure. Existing guard: RSS cap 130000 KiB,
virtual mapping 480000 KiB, one BLAS/OMP thread and 8 s per shard.

    sha256sum -c SHA256SUMS
    ./run-close-total-shard.sh progress 0
    # After authorization, continue serially through shard 8.
    python3 close_total_root.py verify --require-complete progress/*.json

Replay uses exact standard-library Fractions and verifies the full
244-duty prior archive before deriving the 69-element shortlist.
Numerical survivors and unknown are not proofs. See RESULTS.md for the completed exact replay. No new Lean result is claimed.
