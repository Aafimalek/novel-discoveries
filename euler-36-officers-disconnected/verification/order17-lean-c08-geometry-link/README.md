# Euler all-used C08: checked split geometry-to-SAT bridge

Lean checks all 5,788 signed core clause memberships in the actual
geometric formula and excludes diagram [111,1012,1103,2220] from the
all-used size-17 reduction. The original archive has 60,567 rows, and
the exact matched prior SAT endpoint is the clause-order-sorted
EulerBatch.C08CoreSorted, with theorem Euler.Batch.C08.coreUnsat.
It changes the order of clauses, not the signed literals within a
clause.

The final declaration is
LatinGap.PairEncoding.C08Linked.allUsed_geometry_except_c08.
It requires a linear, saturated, size-17 design with minimum
frequency at least two, for which every pair of degree-two labels on
distinct coordinates is used. This excludes C08 alone. It does not
address the other size-17 branches or prove a packing threshold.

The exact syntax identity theorem uses no axioms, signed-formula
conversion uses propext, and the final proof and fresh import both
audit to propext, Classical.choice, and Quot.sound only.

## Replay

Use pinned Lean 4.36.0 and Mathlib
fc4f59e577feb1a4956671bc04ac18aaaf8cd842, with the built Euler
geometry, numbered semantics, and matching prior module
EulerBatch.C08CoreSorted on LEAN_PATH. Run:

    ./replay.sh . C08

The script uses one worker and a 2500 MB interpreter cap by default.
The signed rows are in Init-only C08SignedRows. Each geometric witness
shard imports the rows but not the SAT core; C08Linked imports both
the geometric shards and the core identity. This avoids reloading
the large SAT environment for each shard. The recorded run first
compiled a single geometry shard to verify the split and recorded
an exit status and object digest for every successful stage. A preliminary
tmpfs run stopped after two dependencies due to full storage; the
successful overlay run checked and reused those objects before
continuing from the signed row module. Checkpoint object hashes are audit records; binary artifacts are
not bundled.

If the prior checked module is not available, build the bundled
fixtures/EulerBatch/FactoredDriver.lean and
fixtures/EulerBatch/C08CoreSorted.lean from the fixtures root, adding
it to LEAN_PATH. Both exact alternative CNF/LRAT inputs are included.

To regenerate the untrusted local witnesses and then split the
generated canonical proof sources, run:

    ./prepare_case.sh \
      --original fixtures/EulerBatch/cases/08/original.cnf.gz \
      --core fixtures/alternatives/08/1.cnf --codes 111,1012,1103,2220 --bridge C08 \
      --core-module EulerBatch.C08CoreSorted --core-theorem Euler.Batch.C08.coreUnsat \
      --out ./c08-canonical
    cp ArchiveCoreBlocks.lean split_sources.py ./c08-canonical/
    cp replay-canonical.sh ./c08-canonical/replay.sh
    python3 ./c08-canonical/split_sources.py ./c08-split

Kernel checking requires no Python. Verify staged bytes with
sha256sum -c SHA256SUMS.
