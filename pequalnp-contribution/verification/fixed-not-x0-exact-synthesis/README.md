# Fixed-NOT(x0) normalization for exact DAG synthesis

The previous **UNKNOWN** run stops at its incomplete DRAT receipt. This
is a separate circuit CNF. The bounded run below also returned UNKNOWN. The new bound-14 file is **4,452 variables / 33,655 clauses /
95,111 literals** with SHA-256
`91359c03b06fac5fbf9b5df9d30aa8d05603e76e0ad2c7705de6f673f9ad61ab`.

Starts from the exact 30-frontier encoding in `base.py`. Wires are
(x_0,\ldots,x_7,b=\neg x_0) plus at most 14 AND/OR gates; the NOT gate
itself is not counted. All sharing, depth and fan-out patterns remain
eligible. Only the existence of a normalized representative is imposed.

## Why the stronger constraints are equisatisfiable

1. **Sample-signature equivalence, not a heuristic.** Give each wire its
   30-bit truth vector on the original phase-frontier tests. Whenever a
   gate vector equals an earlier raw or gate vector, replace its uses
   (including the output) by that earlier wire. Whenever it is constant
   on these tests, substitute that constant, propagate the AND/OR constant
   identities, and erase it. Process gates in topological order. No
   gates are added; any remaining nonconstant wire has two nonconstant
   parents and a signature distinct from all earlier wires. Redirection
   preserves each tested evaluation by induction in gate order. This
   does **not** assert equal functions off the samples, but the changed
   circuit is still monotone on each fixed (x_0) phase. The same frontier
   domination theorem lifts its sampled correctness to all 256 inputs.
   A target output is not a constant or any raw wire, so at least one
   gate survives. In particular active repeated parents are unnecessary.
2. **Remove dead gates and reorder legally.** Retain exactly the
   transitive dependency cone of the output. Greedily schedule currently
   available nodes by the smallest current *maximum* parent wire ID.
   Parent wire IDs already assigned to available gates never change.
   A newly available gate must depend on the gate just scheduled, whose
   new wire ID exceeds all previously available parent IDs. Thus the
   maxima are nondecreasing. Both AND and OR are commutative, so each
   smaller parent can be put first. The unique sink of this cone stays
   last in any topological order. This is an ordering constraint, not
   a cap on sharing or a layering assumption.
3. **Identity padding.** After the active prefix, pad to exactly 14
   gates by OR'ing the preceding output with itself. These maxima
   increase, every earlier gate has some later use, and signature
   disequality is imposed only on the active prefix. There is no
   conflict between identity padding and the active restrictions.
4. **Light valid propagation clauses.** On comparable sample masks in
   the same fixed phase, each gate's value is monotone. The graph
   function depends on every original variable: a vertex becomes
   pivotal by fixing an adjacent vertex true and all other vertices
   false. Thus (x_1,\ldots,x_7) each appear, and at least one of (x_0,b)
   appears. These are necessary consequences, not new semantic
   assumptions.

The extra Tseitin markers need only imply a sampled difference; an
active gate requires at least one marker against each earlier gate. A
real normalized circuit extends them by marking the exact differences.
Any model of the stronger formula already satisfies the original
evaluation clauses, so the reverse direction is immediate.

## Static replay

```sh
python3 strong.py raw_x0_14_strong.cnf --selftest
sha256sum -c SHA256SUMS
```

The positive control includes a repeated-parent gate, a wire equal to a
constant on the fixed phases, and a cone using both (x_0) and (b).
Exact normalization removes those sampled redundancies, sorts the
remaining 16 gates and pads once. An independent model validation
then checks every clause and all 256 input evaluations. The 14-gate CNF was generated and fingerprinted. Its
SAT/UNSAT status is unknown after the bounded attempt below. None of these reductions applies unchanged to an arbitrary
NOT operand, and none establishes a gate lower bound for the unrestricted
one-NOT problem or the external obligation.

## Bounded benchmark outcome

Kissat 4.0.4, one worker, reached the 44-second wall-clock cap with no
SAT or UNSAT status. See `status.txt`. The incomplete proof stream
was not a certificate and is not bundled. No new Lean verification
or upstream submission resulted. Regenerate the exact DIMACS file
with `python3 strong.py raw_x0_14_strong.cnf --selftest` or decompress
the bundled gzip; both give the pinned digest above. This research
artifact was developed with AI assistance.
