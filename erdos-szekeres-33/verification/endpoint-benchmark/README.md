# Endpoint-chain benchmark for the 33-point Erdős–Szekeres search

This compares the public Baek–Balko endpoint dynamic program
[`etv_signotope`](https://github.com/jcpaik/erdos-szekeres-sat/blob/61bfbd6f04d73865a5037b0a416d5ba18ce34fbd/lib/erdos.py)
with the compact quadruple-parity encoding. Both use
the sorted one-change packet constraints. No 33-point solve was attempted.

| Points, polygon size | Endpoint DP vars / clauses | Compact parity vars / clauses | DP wall time | Compact wall time |
| --- | ---: | ---: | ---: | ---: |
| 8, 5 | 314 / 1,070 | 126 / 616 | SAT 0.004 s | SAT 0.033 s |
| 9, 5 | 466 / 1,800 | 210 / 1,134 | UNSAT 0.064 s | UNSAT 0.114 s |
| 16, 6 | 3,690 / 24,053 | 2,380 / 22,568 | SAT 0.114 s | SAT 0.116 s |
| 17, 6 | 4,498 / 31,187 | 3,060 / 31,416 | timeout 35 s | timeout 35 s |
| 33, 7 | 45,210 / 570,880 | 46,376 / 4,599,408 | not attempted | not attempted |

These are one local run per instance, same single-threaded Kissat 4.0.4
binary and a Python harness with at most two concurrent instances.
Timing includes solver startup and parsing, but not CNF generation or
certificate output. The small timing differences and 17-point timeouts
do not establish a runtime improvement. The 33-point input reduction is
exact: approximately **8.06× fewer clauses** and **90.8× fewer literal
occurrences** (1,656,968 vs. 150,503,760). The DP CNF is 10,491,402 bytes,
SHA-256 `bfd3f05c6fffff380dc702c4327ef326c453312df7d077d97e1af32fba76640b`.
Compact 33-point counts are combinatorial; that larger file was not emitted.

Both fresh 9-point UNSAT traces independently replayed in DRAT-trim.
Both encodings' 8- and 16-point SAT models were independently checked
against their exact input clauses, packet rule, and parity projections.
At 32 points, fixing all 4,960 signs of the previously audited
classical-style integer witness in the DP produced a SAT model in
0.152 s (40,992 variables, 506,806 clauses). The model independently
satisfied every clause and matched every fixed orientation. This is a
positive control, not a 33-point experiment.

[`EQUIVALENCE.md`](EQUIVALENCE.md) explains why, after projecting
auxiliary variables, these are equivalent signotope relaxations when
the three size parameters are equal. This is not a realizability claim.
`PacketDP.lean` checks the four needed local packet identities in plain
Lean 4.36.0 / Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
The dynamic-program and DIMACS correctness are not claimed as Lean
theorems here.

## Reproduce

```sh
bash fetch_upstream.sh    # downloads two files at a pinned revision and checks their hashes
python3 generate.py | tee generation.tsv
python3 benchmark.py /path/to/kissat --limit 35 | tee benchmark.tsv
python3 fixed32.py
/path/to/kissat dp-fixed-32-7.cnf > fixed32.solve  # exit 10 means SAT
python3 fixed32.py fixed32.solve

# Repeat a positive-control projection check.
python3 check_models.py dp-16-6.cnf results/dp-16-6.log 16 6
# Replay the two 9-point negative controls.
for f in dp-9-5 compact-9-5; do
    /path/to/kissat "$f.cnf" "$f.drat"  # exit 20 means UNSAT
    /path/to/drat-trim "$f.cnf" "$f.drat" -q
done
```

The SAT solver was [Kissat release 4.0.4](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.4).
The checker was [DRAT-trim at 2e3b2dc0](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985).
The upstream files are fetched rather than redistributed. The mathematical
background is [Baek and Balko, The Erdős–Szekeres Conjecture Revisited](https://doi.org/10.1016/j.jcta.2026.106195).
