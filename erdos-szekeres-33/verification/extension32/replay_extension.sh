#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
D="${1:-extension}"
K="${KISSAT:-kissat}"
P="${DRAT_TRIM:-drat-trim}"
python3 extension32.py "$D"
mkdir -p "$D/replay"
for s in $(seq -w 0 32); do
    rc=0
    "$K" "$D/slot-$s.cnf" "$D/replay/slot-$s.drat" > "$D/replay/slot-$s.solve" 2>&1 || rc=$?
    test "$rc" -eq 20
    "$P" "$D/slot-$s.cnf" "$D/replay/slot-$s.drat" -q > "$D/replay/slot-$s.check" 2>&1
    grep -q -a 's VERIFIED' "$D/replay/slot-$s.check"
    printf 'slot-%s ' "$s"
    grep -a -o 's VERIFIED' "$D/replay/slot-$s.check"
done
(cd "$D" && sha256sum points.csv slot-*.cnf replay/slot-*.drat > SHA256SUMS)
