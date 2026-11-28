# Real chain valuation: verification and scope

Lean 4.36.0 strict replay for the endpoint chain dependencies in the
same owner-object ABI as the current real geometry stack, then for the
valuation/propagation connector. The four stage receipts, when present,
identify the exact accepted source and object hashes.

## Scope

The final module's `chainVal (orientations p)` assigns the real
orientation bits and the truth of actual chain existence to the exact
generator's key type. Length-three triple-state aliases agree with the
underlying chain predicates on strictly ordered triples only; pair states
agree at every length without additional ordering assumptions. The ten
semantic propagation fields transfer to the independently declared guard
record, then checked pruning and aliasing give the exact guarded
propagation P for the same valuation as the real sign assignment.
This is a noncomputable existence valuation. No exclusions X, external
DIMACS match, or target UNSAT are proved.

## Fresh overlay replay (original workspace)

Copy `src/` and `run_stage.py` to a fresh overlay with
`out/ES33/` and `tmp/`. Lean resolves a namespaced module from the
first path containing its top-level namespace directory. Populate this
overlay's `out/ES33/` with read-only symlinks to each prechecked
module object in `es33-prelude-legacy-first-two/olean/ES33/` so the
fresh endpoint modules and existing geometry modules share one namespace
directory. Do not link any older Packet/Recurrence/Model objects.
The script checks the pinned Lean binary, the LocalCNF owner key object,
three dependency source hashes, and the literal/direct prerequisite
receipts; it uses one worker, warnings as errors, 2250MB Lean limit and
2310000KiB sampled RSS cap, with an overlay TMPDIR. Run serially:

    python run_stage.py ES33/EndpointPacket 55
    python run_stage.py ES33/EndpointRecurrence 60
    python run_stage.py ES33/EndpointModel 60
    python run_stage.py RealChainValuation 68

Each next stage requires valid receipts and unchanged output hashes from
its predecessors.
