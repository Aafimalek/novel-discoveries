# Lean-checked complete shelf 141

The checked theorem `NineSeparatedSubsetSums.adaptiveShelf141_no_descending_tail`
has type `NoDescendingTail 141`: no positive descending seven-weight
tail can complete the two largest integer weights 148 and 141 to
nine distinct-subset-sum weights. This is the complete shelf, not
just a representative fixed-third case. The compiled axiom audit
lists only `propext`, `Classical.choice`, and `Quot.sound`.
The unconditional real 149 theorem is not claimed.

This archive freezes all 515 exact generated Lean sources,
the precise DAG manifest, all corresponding module logs and successful
source/dependency hash stamps, and the integer penalty data. All source
and log stamp digests were independently recomputed during freeze.
Compiled objects are intentionally not included.

## Dependencies and recheck

Use Lean **4.36.0**, with the same project dependencies and Mathlib
checkout **fc4f59e577feb1a4956671bc04ac18aaaf8cd842**. The
`dependencies/objects.tsv` lists the directly imported prerequisite
modules outside this shelf, with hashes of the actual Lean object
files used. Supplementary source copies are included when available;
these are not new proof claims. Start with the earlier checked
core, four-point/eight-point, cached fixed-third, and adaptive-search
files in their usual project module hierarchy.

Copy the generated `NineSeparatedSubsetSums` files into that Lean
project. Run with the project's ordinary Mathlib `LEAN_PATH`:

```sh
python run-adaptive-queue.py adaptive-141-full.json --jobs 1 --seconds 125 --memory 2850
```

The solver and C++ workload planner are not needed for replay of
these frozen sources. To regenerate, copy these tools plus the
`data` files to the root of the project (the generator reads
`fourpoint-data.json` and any `oct-data-*.json` there), build
`bench-plan` with `g++ -std=c++17 -O3 bench-plan.cpp -o bench-plan`,
then run `python make-adaptive-shelves.py 141 --cost 1600 --oct-cost 3000 --out adaptive-141-full.json`.
Any regenerated input is checked by Lean; neither the external LP
solver nor the C++ planning heuristic enters the theorem.

The preserved logs attest the original build; in a clean checkout,
missing Lean object files cause all relevant jobs to recompile
regardless of existing log stamps. Omitting or raising a resource
cap does not change which statements are checked.

Full frozen sources and logs: [lean-case141-replay.tar.gz](lean-case141-replay.tar.gz), SHA-256 `6c9b2ac1583369c14efcca6a1f2103b9e55bc274c50c0693dff4f2d061cf24a1`.
