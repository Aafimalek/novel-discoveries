# Exact result of the normalized reflected wide split

All 32 guarded shards completed. The nested exact prior verifier
and the standard-library Fraction replay checked all 244 specified
branch duties.

| Branch | New exact rejections | Unresolved by this root test |
|---|---:|---:|
| \(e\le4.5\) (closed relaxation of the mathematical endpoint) | 0 | 122 |
| \(e\ge6\) | 0 | 122 |

Both branches must have exact certificates to exclude one full
wide orientation. Their exclusion intersection is empty. A whole
central orientation would additionally require an independently
verified close certificate. The checker separately replays all 73
previous close certificates and checks that intersection as well.
Thus 122 wide, 49 close, and 122 whole orientations remain
unresolved. All numerical statuses are survivors of the LP
relaxations, not valid feasible examples or chamber certificates.

For all cases the verifier checks the exact inherited row prefix
and the single permitted row \(2X-2x_7\le9\) or
\(x_7-X\le-6\). No q-slot, close-duty, or alternative numeric
run was conducted. The written \([4.5,6)\) elimination and finite
top-pattern replay remain independent of this inconclusive LP test.

    sha256sum -c SHA256SUMS
    python3 check-complete-reflected-split.py

Raw receipts for all successful 8 s / 130000 KiB RSS /
480000 KiB virtual guards are included under timing/.
