# Eight-vertex edge detection: restricted circuit architecture checks

This is partial work on P vs NP desk unit **L-meta-34819**, not a proof of
that unit or a submission to the desk. The question is whether allowing a
single NOT gate can beat every monotone AND/OR circuit for the edge
function of this specific graph. The unrestricted statement remains open.

The graph has edges 03, 14, 24, 05, 15, 35, 16, 26, 46, 07, 27, 37,
47 and 57. A 16-gate monotone circuit is the OR of the five biclique
terms with sides

    [2,4] × [6,7]
    [5]   × [1,7]
    [0,3] × [5,7]
    [1,2] × [4,6]
    [0]   × [3]

where each term is an AND of the ORs of its sides, and the final OR
uses four gates. Consequently a refutation would need a one-NOT
circuit with at most 15 gates.

## Two architecture-specific checks

1. In the architecture whose output is an OR of biclique terms, with
   binary pure-OR wires arbitrarily shared among sides, the minimum
   gate count is 16. There cannot be two necessary instances of the
   same pure-OR wire or the same biclique term. Thus choose one bit per
   selected side wire and per selected biclique term. Each term must
   have its sides, a nonsingleton side must be the union of two
   strictly smaller nonempty available sides, and every true edge
   must belong to a selected term. Multiple uses and overlapping
   splits are allowed. An output OR of t distinct terms needs t−1
   two-input gates even when regrouped in a DAG; together with the t
   term gates this is 2t−1. The CNF below encodes these conditions and
   the gate budget. The saved DRAT refutation is independently
   replayable. It does not rule out general monotone AND/OR DAGs.
2. The exact enumeration also checks unshared formulas of the form
   P OR (Q AND NOT H), where Q is one biclique with both true and
   false pairs, H is the OR of bicliques covering exactly Q's false
   pairs, and P is an OR of legal bicliques. Covering the required
   true inputs gives an exact bounded finite dynamic program. The
   best formula of this restricted form uses 19 gates. This is not
   an unrestricted lower bound for circuits with one NOT.

## Replay

The opposite architecture is not decided by these checks. No result
here has been checked in Lean. From this directory, with Python 3 and
the independent open source DRAT verifier:

```sh
sha256sum --strict -c SHA256SUMS
python3 generate_cnf.py 15
cat verified-proof.drat.gz.part-* | gzip -dc > verified-proof.drat
drat-trim monoshared15.cnf verified-proof.drat
python3 pure_formulas.py
```
