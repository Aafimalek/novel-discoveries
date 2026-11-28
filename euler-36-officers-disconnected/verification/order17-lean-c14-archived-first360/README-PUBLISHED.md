# Checked C14 exact sorted archive through 360 learned clauses

This release extends the exact initial archive theorem to
`Euler.C14.Production.exactArchiveThrough9185`, covering all 8,825
original clauses and the first 360 of 5,085 learned additions. The final
raw learned ID is 11088. Eleven additional slices checked 9,271 exact hint
references. The top theorem uses only `propext`, `Classical.choice`,
and `Quot.sound`.

Rebuild the checked source dependencies in this order:
[first48 global index](../order17-lean-c14-global-first48),
[first72 exact archive](../order17-lean-c14-archived-first72),
[first288 prefix](../order17-lean-c14-archived-first288),
then the archive in this folder. The preserved per-slice receipts and
hash manifests pin the exact checked stages. No terminal empty clause
or C14 geometry exclusion has been proved in this release.
