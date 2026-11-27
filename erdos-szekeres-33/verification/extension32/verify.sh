#!/usr/bin/env bash
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
D="${1:-es-extension-replay}"
P="${DRAT_TRIM:-drat-trim}"
mkdir -p "$D"
D="$(cd "$D" && pwd)"
(cd "$HERE" && sha256sum -c ARCHIVE.sha256)
python3 "$HERE/extension32.py" "$D"
cmp "$D/points.csv" "$HERE/points.csv"
(cd "$D" && sha256sum -c "$HERE/DIMACS.sha256")
tar -xzf "$HERE/certificates.tar.gz" -C "$D"
(cd "$D" && sha256sum -c "$HERE/CERTIFICATES.sha256")
"${CXX:-g++}" -std=c++17 -O2 "$HERE/witness_hull_check.cpp" -o "$D/witness_hull_check"
"$D/witness_hull_check" "$D/points.csv"
mkdir -p "$D/replay"
for s in $(seq -w 0 32); do
    "$P" "$D/slot-$s.cnf" "$D/certificates/slot-$s.drat" -q > "$D/replay/slot-$s.log" 2>&1
    grep -q -a 's VERIFIED' "$D/replay/slot-$s.log"
    echo "slot-$s: VERIFIED"
done
