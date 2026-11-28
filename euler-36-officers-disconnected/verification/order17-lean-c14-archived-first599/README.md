# Static C14 exact ID11641 late polarity recut
No Lean or Git ran. This is a new isolated workspace. Restored read-only
frozen456 copies the original checked source/audit/cache archives and
preserves every prior source/object/log record. The earlier 19 segments
are byte-identical; they advance the common conditional polarity state
to NegBelow ... 497 after 456 hints. The actual contiguous archive stays
at exactArchiveThrough9423 (598 learned clauses).

The actual raw ID11641 and archive span, exact target, all 510 hints
with known literal indices, and ending conflict are unchanged. Only
[456,509) is repartitioned. The late proof proxy per hint is exact
premise literal count + the sum of floor(max(0,index−41)/64) over
known arguments; this gives higher cost to part of the later linear
polarity-array normalization proxy. Ordinary groups use at most six
hints and 150 proxy units; isolate width >=30 or per-hint cost >=110.
The resulting 15 leaves include expected 4–6-hint groups plus narrower
ones for wide premise rows. The first late leaf is [456,462), 32
premise literal arguments/proxy 126. The max 55-literal premise is
isolated at [481,482), proxy 245. All metadata are in generated/row11641.json.

The new composer only changes the split points/import list, uses the
same balanced proof expression and identical close implementation, and
retains exact typed result forall base, Slice base rowAt 9423 9424.
The last archive attachment source is byte-for-byte unchanged. A
separate audit module is ready to report all 34 actual segment results,
the terminal conflict, step and final conditional slice individually.
None of the new leaves or glue is verified by this staging.

Old failed 24-hint [456,480) had 182 literal args, versus 48–118 for
late completed 24-hint leaves that took about 9–12s. The normalized
cost for it and late recuts is listed in work-proxy.log. Per-leaf work
should be much smaller except for individual wide literals; compiler
startup and import costs are repeated for 15 leaves. Very rough
planning estimate 45–90s including glue from prior timings, not a
runtime guarantee. A single wide leaf can still hit the 17s cap.
If so stop and preserve prior receipts, no timeout increase.

./resume-recut.sh defaults to static checksum/preflight. Only after
a new heavy authorization, ./resume-recut.sh --execute uses global
nonblocking lock, strictly ordinary pinned Lean 4.36, overlay TMPDIR,
-j1, -M2450, warnings as errors, unchanged 17s per leaf and 98s absolute
wall guard. It reuses frozen exact 456 evidence and requires all
project-visible pinned input/source/object/log digests, including
immutable through9423. A later restart only skips a newly completed
segment if its source/object/log receipt matches. There is no claim
from a partial state, and all exact closure proof/axiom lines are
required before counting the 599th learned row.

Source tar does not duplicate read-only local cached objects. Recreate
frozen456 by extracting the prior three frozen archives into it:
source 3099fecf7189208a94137a7c7ad6a33090fa021221b686ff42ae98b7e7de76d2,
audit 615a826aa4f686a16590fc66bef60b5b696f7b0df027d20197aecd01cb6491fe,
local-cache d106aad252dd7cd634270e2701258627398c8f856f222a384acaab67cbf6cdc6.
