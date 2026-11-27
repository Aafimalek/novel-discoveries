# Adaptive Lean queue for the remaining 149 shelves

This is a reproducible generator and runner, **not** verified coverage of
any new shelf. It works with the existing Lean 4.36 project containing
the cached centered-search, packed four-point and packed eight-point
helpers. Compile the included `CachedSearchTree.lean` first if it is
not already in the project. Its split-composition theorem was checked.

Copy the Python scripts, C++ estimate source, and integer JSON data
to the root of that project. Keep its Lean/Mathlib dependencies in
`LEAN_PATH`, or run the scripts under its usual Lake environment.

```sh
g++ -std=c++17 -O3 bench-plan.cpp -o bench-plan

# Two representative third-weight branches, not full shelves.
python make-adaptive-shelves.py 138 --third 137 --out adaptive-138-example.json
python make-adaptive-shelves.py 147 --third 146 --out adaptive-147-example.json
python run-adaptive-queue.py adaptive-138-example.json --jobs 2

# Any complete shelf from 121–147; omit --third to cover all of it.
python make-adaptive-shelves.py 121 --out adaptive-121.json
python run-adaptive-queue.py adaptive-121.json --jobs 2
```

The supplied representative oct-point JSONs allow those examples to
regenerate without the numerical LP solver. To generate missing
eight-point tables, install SciPy, or use `--no-oct` to use only the
supplied four-point tables. The generator can run on any shelf
114–147, but use a clean matching checkout and avoid racing against
another build of the same shelf. File locks guard each shelf while a
generator or verifier operates locally.

The generator selects an exact integer four-point moment cutoff and,
for expensive third-weight branches, can choose a stronger eight-point
cutoff. An untrusted C++ estimate drives adaptive splitting beyond the
third weight and groups small numerical leaves into batches. At each
split the generated Lean theorem checks **exact equality of the
enumerated child list**, and each numerical leaf uses
`decide +kernel`. The C++ estimates and Python lists need not be
trusted. With `--cost`, lower the heuristic node cap if kernel
reduction on a numeric leaf exceeds available resources.

The runner schedules declared dependencies, keeps a separate log and
successful source/dependency fingerprint per module, and can resume
with unchanged inputs. It prints `VERIFIED SHELF` only when the entire
scheduled shelf and final symbolic no-tail theorem build without
`sorryAx`; with `--third` it says `VERIFIED REPRESENTATIVES ONLY`.
Use one or two workers depending on available memory; each Lean
process has a separate memory and wall-time cap. A failed proof or
resource limit is not an exclusion.

## Generated examples (not replayed)

- At (138,137), the C++ estimate drops from 218,762 states with the
  four-point bound to 22,209 with the eight-point cutoff 128,810.
  Splitting estimates at most 1,202 states in an individual leaf,
  using 16 batched leaf modules and one join module.
- At (147,146), the estimate drops from 1,290,461 to 239,043 with the
  eight-point cutoff 131,753. The largest planned leaf is 1,572
  states, using 163 batched leaf modules and seven join modules.

These are heuristic workload estimates; the high representative
manifests are generated plans, not completed Lean runs. The
unconditional real 149 theorem still requires every actual remaining
shelf and an assembled final theorem.

## Checked runner pilot

The included `examples/checked-121-107` archive is a replayed
instance for just **(121,107)**. The exact generated DAG had 16
modules, two numerical/geometric layers, and four certified internal
joins. Its final `adaptive121Third107` theorem depends only on
`[propext, Classical.choice, Quot.sound]`. This tests generation,
topological compilation, closed leaf decisions, exact child-list
checks, and geometric composition, but does not close shelf 121.

To regenerate this specific test:

```sh
python make-adaptive-shelves.py 121 --third 107 --cost 6 --no-oct --out adaptive-121-tiny.json
python run-adaptive-queue.py adaptive-121-tiny.json --jobs 1
```

The [complete source-and-data replay archive](adaptive-replay.tar.gz) has SHA-256 `34ff28ea6d77519d747f3fbb2d87f9b09ddb2bdb4168e55595ee599a78ea6a8d`. The generated data described above is supplied in this archive rather than duplicated in this directory.
