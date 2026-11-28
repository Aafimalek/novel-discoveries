# Exact close-triple total-row screen

The nine deterministic guarded batches completed all 69 previously
unresolved close-branch duties. The final Fraction-only verifier
replays their full prior 244-duty partition and certifies this result:

| Case scope | New exact exclusions | Not excluded by this screen |
|---|---:|---:|
| Close triple \((x_7,x_8,x_9)=(X-1,X,X+1)\) | 20 | 49 |
| Wide terminal pair | Not tested | 122 inherited |

Accounting for the earlier 53 close-only exact certificates, the
new close certificates leave 49 unresolved close and 122 unresolved
wide duties, a total of 171 duties across 122 central orientations.
**No new whole central orientation is excluded.** No lower bound
of 150 or complete floor-148 exclusion is claimed. The 49 were
only numerical survivors of this relaxation, not feasible
configurations or certified full sign chambers.

All 20 rational certificates use the strong written row
\(\sum_{i=1}^6 x_i\ge3X+109\) with a positive multiplier, and
all have weighted RHS \(-1\). The top-three sign pattern among
these exact closes is +-- (10), ++- (8), +++ (1), and --- (1).
The earlier analytically excluded close word -----+++- is
included in the 20 (not added to the count); its exact vector
has new-row multiplier \(1/118\) and does not use a strict
inherited row.

Nine serial guard receipts are included. Child elapsed times sum
to 6.08 s; maximum child elapsed time was 0.93 s; maximum audited
child peak RSS was 60,840 KiB. All guards passed. No wide or q-slot
follow-up was run. The written theorem on which the new row depends
is in close-triple-slot-grammar.md and is not formalized in Lean.

Standard-library exact replay:

    sha256sum -c SHA256SUMS
    python3 check-complete-close-total.py
