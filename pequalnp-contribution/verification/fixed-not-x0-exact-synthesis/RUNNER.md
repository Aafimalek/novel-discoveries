# Static bounded runner (not executed)

With explicit authorization and one available solver slot:

```sh
python3 run_bounded.py \
  --solver /path/to/pinned/kissat \
  --checker /path/to/independent/drat-trim \
  --run-dir /path/on/overlay/fresh-run
```

The parent must already exist and have at least 512 MiB free. The run
directory must not exist. The solver uses one worker, at most 44 seconds,
120 MiB address space, and no output file above 128 MiB. The exact strong
CNF is pinned and checked before and after the run. The script records
binary hashes. If SAT is reported cleanly, it checks every generated
clause and all 256 circuit evaluations before reporting verified SAT.
If UNSAT is reported cleanly and a proof exists, it runs a separate
bounded exact certificate replay only after the solver exits. A timeout,
signal, incomplete file, or failed decode/replay is **UNKNOWN**.
No statement about arbitrary negation placement follows.
