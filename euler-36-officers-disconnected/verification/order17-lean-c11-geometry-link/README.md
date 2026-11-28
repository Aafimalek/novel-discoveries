# Euler all-used C11: checked split geometry-to-SAT bridge

Lean checks all 5,250 signed core clause memberships in the actual
geometric formula and excludes diagram [111,1012,2201,1320] from the
all-used size-17 reduction. The original archive has 60,567 clauses.
The exact matched prior SAT endpoint is EulerBatch.C11CoreSorted,
with theorem Euler.Batch.C11.coreUnsat. Its input reorders clauses,
not the signed literals within a clause.

The final declaration is
LatinGap.PairEncoding.C11Linked.allUsed_geometry_except_c11.
It requires a linear, saturated, size-17 design with minimum frequency
at least two, for which every pair of degree-two labels on distinct
coordinates is used. It excludes this one geometric case, not the
rest of the size-17 problem or a packing threshold.

The exact syntax identity theorem uses no axioms, signed-formula
conversion uses propext, and the final proof and fresh import both
audit to propext, Classical.choice, and Quot.sound only.

## Replay

Use pinned Lean 4.36.0 and Mathlib
fc4f59e577feb1a4956671bc04ac18aaaf8cd842, with the built Euler
geometry, numbered semantics, and matching prior module
EulerBatch.C11CoreSorted on LEAN_PATH; set LEAN_BIN to the pinned
binary and run from a workspace-overlay copy. When a compiler slot
is available, use:

    EULER_C11_LEAN_SLOT=approved ./run-checkpoint.sh

The script uses one worker, a 2500 MB interpreter cap, and capped
per-file stages. The checked runtime had a bounded 405-second outer
wrapper and the same staged compilation sequence. It used the
previously checked exact generic block module and then built the
C11 code, signed rows, first membership shard, raw SAT identity,
remaining shards, final link, and fresh import audit. The per-step
receipts and object checks are included, but binaries are not bundled.
The standard script has a 355-second wrapper and can resume later
from completed digest-checked modules if it reaches its deadline.

The signed rows live in Init-only C11SignedRows. The geometry shards
import the signed rows but not the large core proof. The final
link imports both. This is the same split construction used in C08.

If the prior checked core module is not available, build the bundled
EulerBatch.FactoredDriver and EulerBatch.C11CoreSorted from the
fixtures root, with the pinned Mathlib on LEAN_PATH. The included
CNF and LRAT are the exact prior inputs. If using the rebuilt,
checked module instead of the cached binary digest in the logs,
set C11_CORE_REBUILT=1.

To regenerate the untrusted local witnesses and then split them:

    ./prepare_case.sh \
      --original fixtures/EulerBatch/cases/11/original.cnf.gz \
      --core fixtures/alternatives/11/1.cnf --codes 111,1012,2201,1320 --bridge C11 \
      --core-module EulerBatch.C11CoreSorted --core-theorem Euler.Batch.C11.coreUnsat \
      --out C11-canonical
    cp ArchiveCoreBlocks.lean split_sources.py C11-canonical/
    cp replay-canonical.sh C11-canonical/replay.sh
    python3 C11-canonical/split_sources.py C11-split

Kernel checking requires no Python. Verify staged bytes with
sha256sum -c SHA256SUMS.
