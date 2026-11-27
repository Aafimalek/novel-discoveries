# Reproduce or audit the exact order-16 cases

This branch saves the CNF generators, case split, and hashes. It does not carry the compressed trace binaries. The authoring run saved the ten independently verified traces; someone else can generate a fresh proof for any regenerated formula, then verify it. The formula hashes must match; a fresh solver trace is not expected to have the same hash.

Install `python-sat==1.8.dev24`, get the pinned DRAT-trim version cited in the case note and Kissat 4.0.4, and run from this directory:

```sh
python regen16.py m1 /tmp/euler16-m1.cnf
sha256sum /tmp/euler16-m1.cnf
kissat /tmp/euler16-m1.cnf /tmp/euler16-m1.drat
# Kissat's exit code 20 means UNSAT.
drat-trim /tmp/euler16-m1.cnf /tmp/euler16-m1.drat -q
```

Repeat for the ten IDs in `cases16.tsv`. Compare the resulting DIMACS hashes against `F16.sha256`. An independently replayed DRAT result is not an end-to-end Lean proof.
