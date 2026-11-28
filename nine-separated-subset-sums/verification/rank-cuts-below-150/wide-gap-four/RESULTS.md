# Exact wide e>=4 replay result

Completed all 16 serial guarded batches, covering all 122
wide root duties. Each model is exactly its previously checked
wide e>=3 model plus the one added row \(x_7-x_8\le-4\).
There were **zero new exact wide rejections**. All 122
numeric survivors are merely surviving LP relaxations, not
certified feasible chambers or feasible nine-weight examples.
No change to the counts of 122 wide, 49 close, or 122 whole
residual orientations. No e-band, q-slot, or close-branch
numeric follow-up was performed.

    sha256sum -c SHA256SUMS
    python3 check-complete-wide-e4.py

The written e>=4 statement and optional static top-pattern
compatibility table are separately under written/. Those
structural results do not themselves close the remaining
wide slice.
