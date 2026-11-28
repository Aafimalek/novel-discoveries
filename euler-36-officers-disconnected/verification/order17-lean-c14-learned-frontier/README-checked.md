# Lean-checked C14 learned-frontier composition pilot

All six local modules passed warning-as-error in ordinary Lean 4.36.0,
serial, with a 2,300 MB configured process limit and per-module bounds.
This is a checked composition of three RUP additions under typed input
proofs, not a complete C14 refutation, a recovery of the monolithic
attempt, or a geometric exclusion. The generic interface is the
separately checked C10 interface with an unused-variable lint fix.

## Trace variant and bounds

Use the **sorted** 8,825-row core and 4.5 MiB LRAT
`/tmp/euler-extra/alternatives/14/1.cnf` and `1.lrat`, the
archive files consumed by `C14CoreSorted.lean`. The bounded search
reads at most 192 KiB of LRAT by default. It stops after precisely
167,350 bytes and addition number 432, the first addition in this
variant with a positive reference to any earlier learned row. It
does not scan the whole trace. An exploratory comparison found an
earlier learned dependency in the **different** original 18 MiB
`core.lrat`, but that variant is not used in these proof files.

The selected C14 archive is the all-low-pairs-used diagram
`aus-0111_1012_2201_3320`. This pilot does not substitute C10's
degree-one geometry or formulas.

## Two exact source projections

- **Producer A**: one actual contiguous byte interval containing
  additions 10801 and 10802 (numbers 85 and 86) and the intervening
  actual deletion. Each addition uses 27 original live hints,
  with 30 distinct exact original rows overall. This 296-byte
  projection yields exactly two learned boundary clauses:
  - ID 10801: `[-1346, 1352, -1358, -1364]`.
  - ID 10802: `[-1346, 1352, -1358, 1364]`.
- **Consumer B**: actual addition 11163 (number 432), a 39-byte
  row. Its only hints, in order, are 10801 and 10802. They survive
  the intervening 345 additions and their deletion rows. The output
  is the nonempty clause `[-1346, 1352, -1358]`. Under falsification
  of the three target literals, row 10801 forces -1364 and row
  10802 is then a conflict.

The script validates exact earlier liveness across all scanned
events and performs literal-by-literal unit/conflict checks for
the three selected proof additions. It does not proof-check the
345 omitted additions or claim a complete chain through the gap.
Those additions need not be supplied to prove this projected
consumer: no consumer hint refers to them. This is the point of
a small cross-boundary dependency test instead of monolithic replay.

## Typed theorem target

`EulerC14Producer.step : Transformer inputs boundary` and
`EulerC14Consumer.step : Transformer boundary output` independently
import the common signed data and checked bounded RUP driver. They do not
import one another or any earlier proof module. Each local
`exact_input_formula` pins the driver's actual small context to
the intended typed frontier, and the usual kernel accepted
its generated RUP proof terms. A third module then checks
`Euler.RupFrontier.C14.composed : Transformer inputs output` and
`fromCommonBase`, connecting the two producers to a consumer
which requires those genuinely learned clauses.

The assembly assumes actual proofs of the exact original input
clauses from whatever common base is chosen. The Python row and
liveness audit cannot discharge those premises in the kernel.
Also, neither slice derives an empty clause. A full refutation
would have to establish exact base-membership for every needed
input, scale the dependency graph to its terminal row, and
measure final transitive-import/memory cost. No proof by trusting
a supplied ID, manifest or digest is proposed.

## Repeat

Run `extract_two_slice.py SORTED_CORE.cnf SORTED_TRACE.lrat OUT_DIR`
to regenerate the short source projections, the exact literal and
offset manifest, and the four particular Lean sources. Use `replay-checked.sh`
with Lean 4.36.0 and pinned Mathlib on an overlay directory. The
absolute input path in the script is intentional for `include_str`.
`compile-order.txt` records the serial order. Producer and consumer
exact-input formula equalities have no axioms; each step has only
`propext`. The composed transformer and its common-base transfer have
only `propext, Quot.sound`. No native or admitted axioms were used.
The independent Python audit is separate from these kernel proofs.
