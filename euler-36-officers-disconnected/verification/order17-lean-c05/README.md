# Euler original size-17 formula C05: complete Lean refutation

`Euler.Batch.C05.branchNoAssignment` excludes every valuation of the exact
numbered original `aus-0111_1012_2201_3120`: 60,567 clauses, 10,646
variables, SHA-256 `520fbb761902f7443caef5b029e12daba8034d8e7696b496a853c8b6bb2fcdec`.
Lean checked the pure-RUP 5,036-clause core and its ordered inclusion
in the full parsed formula; the axiom audit lists only `propext`.

A separate [identity audit](loaded-formula-identity.log) matched all
60,567 ordered model clauses directly to the formula declaration
refuted in Lean. That audit is not a kernel proof of formula equality
or a DIMACS parser proof. With this case, 13 out of 56 original size-17
numbered inputs have full Lean refutations, including 13 of the 17
all-used cases. Other cases remain open in Lean.

[Replay archive](euler-c05-replay.tar.gz) · SHA-256 `dd33080a24917264bdbc0edc7d4fd0a235e0fb45d53d1bc4715459c5b9b9a232`.
Extract it and run `bash replay.sh` with Lean 4.36.0 and
the matching prebuilt Mathlib dependencies in `LEAN_PATH`.
