# Verified wide split using the reflected signed-rank gap theorem
The compiled note is in reflected-wide-bands.pdf; its source is reflected-wide-bands.tex. Extract exact-reflected-replay.tar.gz for the complete replay and SHA256SUMS.

For the mathematical derivation and exact finite sign-pattern
replay, see written/README.md. The theorem applies to normalized
wide candidates in the established floor-148 slice, not to all
real weights. It removes the entire interval \(4.5\le e<6\)
where \(e=X-x_7\). The lower LP uses the conservative closed
endpoint \(e\le4.5\); the upper uses \(e\ge6\).

This exact screen is completed (see RESULTS.md). It covers the same 122
wide central sign words as the verified preceding e>=4 root run
(included under prior-wide-e4/). Each branch appends only one row
to that exact prior model: \(2X-2x_7\le9\) or \(x_7-X\le-6\).
No new slot, prefix, or stronger affine excess row is added.
Full replay independently checks the prior archives and exact
row prefixes. Both branch certificates are needed to count
a new exact wide orientation; neither one alone is counted.
No close duty is tested, and no whole-orientation claim is made
without the separately verified close intersection.

Run only with separate authorization, one guarding numerical
process at a time. There are 16 shards per branch, with eight
cases except the final two, so complete replay checks 244
duties. Standard caps are 8 s, 130000 KiB audited maximum RSS,
480000 KiB virtual mapping, and one BLAS/OMP thread.

    sha256sum -c SHA256SUMS
    ./run-reflected-shard.sh progress low45 0
    # After authorization run both branches 0..15 serially.
    python3 reflected_split.py verify --require-complete progress/*.json

Exact certificate replay is standard-library Python; it uses
no SciPy. Numeric hints, if generated later, are evidence of
exclusion only when a rational vector has independently replayed.
No Lean result is claimed here.
