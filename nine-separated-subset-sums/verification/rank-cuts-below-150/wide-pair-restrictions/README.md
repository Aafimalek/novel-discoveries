# Bounded wide-branch test of the written e>=3 restriction

This screen tests exactly 122 normalized wide branch duties. It appends
one row to the inherited wide root relaxation:
\(e=X-x_7\ge3\). The written derivation is in wide-pair-restrictions.md.
The conditional seventh-sign identities for \(3\le e<4\) are not
encoded here and their branches are not run. No q-slot expansion.

The prior exact replay audits all earlier normalized orientations and
the full two-way split, then the 20 new close certificates. Any newly
closed wide duty is counted as a whole orientation only if its close
duty also has a separately verified certificate in those prior files.
Uncertified numerical statuses do not count.

One solver process, 130000 KiB RSS guard, 480000 KiB virtual mappings,
one numerical thread and 8 seconds per shard. Sixteen disjoint
eight-case shards except the last with two. New output belongs in a
fresh workspace overlay directory.

    sha256sum -c SHA256SUMS
    ./run-wide-shard.sh progress 0
    # Continue the designated batch serially through shard 15.
    python3 wide_e3.py verify --require-complete progress/wide-e3-*.json
