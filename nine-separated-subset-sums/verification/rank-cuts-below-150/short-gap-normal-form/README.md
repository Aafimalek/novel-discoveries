# Short-gap normalization for separated subset sums

[Written proof (PDF)](short-gap-normal-form.pdf) · [TeX](short-gap-normal-form.tex)
· [Exact normalized floor-148 replay](normalized-floor148-replay.tar.gz)

In any unit-separated labeled subset-sum order, adjacent gaps below 2
can only occur in one two- or three-weight block. Compress that block
to unit gaps about its fixed mean to preserve every labeled comparison
and all unit separation without increasing the largest weight.

In the final nine-weight slice below 150, this makes the top gap
exactly 1 and reduces the other nearby gap to either 1 or at least 2.
A midpoint construction also proves (x_6ge44+22(x_9-x_8)).
The exact screen used the normalized top gap and several valid bounds;
the two new rational certificates need only (x_6ge66) among
the new rows, so neither depends on normalization. In total 390 of 512
central orientations are excluded, leaving 122 unresolved. The further
terminal pair/triple split has not been tested in the published screen.

Run `python3 check_gap_examples.py` to replay exact rational labeled-order
examples. For the certificate-based screen, unpack the archive and run:

```sh
cd replay
sha256sum --strict -c SHA256SUMS
python3 check-complete-normalized.py
```

This is a handwritten theorem with exact finite checks, not a Lean result
and not a lower bound of 150.
