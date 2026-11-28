# Verified floor-148 root screen

The complete deterministic queue processed all 512 central orientations
in 64 disjoint shards. Exact rational replay rejected **388**, leaving
**124 unresolved by this screen**. The latter are not candidate examples
or certified feasible chambers. They were numerical survivors of the
relaxation; no numeric status was used as proof.

Relative to the specified earlier certified root and rank-moment packet
(294 plus 22 disjoint exclusions), all 316 previous exclusions were also
certified here, and this run yielded another **72** under the extra
floor-148 assumptions. No optional seven-sign slot was run, and the
optional stronger real-six/real-seven bounds, scaled lattice cuts, and
flank-witness cuts were not encoded. In particular, this is not an
exclusion of the whole floor-148 slice.

From this directory, standard Python only:

    sha256sum -c SHA256SUMS
    python3 check-root-queue.py certificates
    python3 compare-prior.py

Every reported rejection uses exact Fraction arithmetic. The complete
coverage checker reconstructs the 64 fixed index ranges, then replays all
certificate rows freshly. The comparison script also rechecks both prior
certificate layers before measuring overlap.

The numerical hint generator ran serially with one child per shard, a
130000 KiB process-group resident kill threshold (5 ms polls and an RSS
high-water audit), a 480000 KiB per-process virtual address limit, and at
most 8 s elapsed per shard. All 64 successful attempts are preserved in
timing/: their elapsed times sum to 41.32 s, the slowest was 1.04 s,
and the largest child peak RSS was 61088 KiB. The earlier restrictive
140 MiB virtual-only experiment failed at SciPy shared-library import
and produced no shard; it is not represented as part of this run.
