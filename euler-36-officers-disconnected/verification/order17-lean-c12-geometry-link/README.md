# Euler all-used C12: checked split geometry-to-SAT bridge

Lean checks all 7,089 signed core clause memberships in the actual
geometric formula and excludes diagram [111,1012,1203,2320] from the
all-used size-17 reduction. The original archive has 60,248 clauses.
The exact matched prior SAT endpoint is EulerBatch.C12CoreSorted,
with theorem Euler.Batch.C12.coreUnsat. Its input reorders clauses,
not the signed literals within a clause.

The final declaration is
LatinGap.PairEncoding.C12Linked.allUsed_geometry_except_c12.
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
EulerBatch.C12CoreSorted on LEAN_PATH; set LEAN_BIN to the pinned
binary and run from a workspace-overlay copy. When a compiler slot
is available, use:

    EULER_C12_LEAN_SLOT=approved ./run-checkpoint.sh

The script uses one worker, a 2500 MB interpreter cap, and capped
per-file stages. The checked runtime had a bounded 398-second outer
wrapper and the same staged compilation sequence. The initial launcher guard exposed a case-substitution typo in the pinned
commit string; it was corrected before any C12 proof file ran, and the
manifest diff records the launcher-only change. The run used the
previously checked exact generic block module and then built the
C12 code, signed rows, first membership shard, raw SAT identity,
remaining shards, final link, and fresh import audit. The per-step
receipts and object checks are included, but binaries are not bundled.
The standard script has a 355-second wrapper and can resume later
from completed digest-checked modules if it reaches its deadline.

The signed rows live in Init-only C12SignedRows. The geometry shards
import the signed rows but not the large core proof. The final
link imports both. This is the same split construction used in C08.

If the prior checked core module is not available, build the bundled
EulerBatch.FactoredDriver and EulerBatch.C12CoreSorted from the
fixtures root, with the pinned Mathlib on LEAN_PATH. The included
CNF and LRAT are the exact prior inputs. If using the rebuilt,
checked module instead of the cached binary digest in the logs,
set C12_CORE_REBUILT=1.

To regenerate the untrusted local witnesses and then split them:

    ./prepare_case.sh \
      --original fixtures/EulerBatch/cases/12/original.cnf.gz \
      --core fixtures/alternatives/12/1.cnf --codes 111,1012,1203,2320 --bridge C12 \
      --core-module EulerBatch.C12CoreSorted --core-theorem Euler.Batch.C12.coreUnsat \
      --out C12-canonical
    cp ArchiveCoreBlocks.lean split_sources.py C12-canonical/
    cp replay-canonical.sh C12-canonical/replay.sh
    python3 C12-canonical/split_sources.py C12-split

Kernel checking requires no Python. Verify staged bytes with
sha256sum -c SHA256SUMS.
