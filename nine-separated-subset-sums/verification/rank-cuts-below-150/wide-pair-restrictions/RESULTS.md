# Exact replay of the wide \(e\ge3\) root test

All 16 guarded shards completed and the pure Fraction checker replayed
all 122 wide duties and the full prior archive.

The new \(x_8-x_7\ge3\) row gave **zero recorded exact wide-duty
rejections**. All 122 remained numerical survivors of the relaxation,
which is not a proof of their actual feasibility. The earlier 49
close duties remain unresolved and **no additional whole central
orientation is excluded** (122 remain). No \(e\ge4\) or lower-bound-150
claim is made. The written \(3\le e<4\) mixed-sign implications are
neither assumed in these LPs nor tested by a q-slot expansion.

All existing per-shard process guards passed; raw times and RSS
receipts are in timing/. Exact independent replay:

    sha256sum -c SHA256SUMS
    python3 check-complete-wide-e3.py
