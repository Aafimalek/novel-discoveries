# A barrier for intertwined branches in the width-three project

This package contains two different results; neither solves the width-three
1/3–2/3 conjecture.

- **Actual posets (written proof):** `notes.md` gives necessary constraints on
  the low/high split of a hypothetical no-balanced good-pair branch partitioned
  into two chains. As an application, it gives a sufficient probability bound
  when the exclusive upset minus its root is a chain and one additional vertex.
  The precise good-pair and probability assumptions are in the note. These
  statements are not fully formalized here.
- **Synthetic histogram (Lean):** `LateHistogramBarrier.lean` verifies a
  four-component, antitone cutoff mixture for 3×4 arms, with root-first
  probability 7/43, no balanced pair, and a majority order in which a follows
  the first arm vertex. Lean also verifies failure of a conditioned XYZ
  inequality. This is a barrier to using cut monotonicity alone; it is not
  an actual-poset counterexample. The fact that all marginal XYZ inequalities
  hold was checked by exact integer Python enumeration in
  `check_marginal.py`, not by the Lean file.

The Lean file imports only Init. Validation was with Lean 4.36.0, one worker,
and a 650 MB Lean memory cap. Run:

    lean -j1 -M650 --json LateHistogramBarrier.lean
    python3 check_marginal.py
    sha256sum -c SHA256SUMS

`build2.log` records the successful Lean axiom audit; the named theorems
depend only on `propext` and, where reported, `Quot.sound`.
`marginal.log` is the separate Python output. The package contains no
compiled files or solver outputs used as Lean proof oracles.
