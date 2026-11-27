#!/usr/bin/env bash
set -eu
source_dir="$1"
dest="$2"
P="${DRAT_TRIM:-drat-trim}"
mkdir -p "$dest/certificates" "$dest/logs"
for s in $(seq -w 0 32); do
    "$P" "$source_dir/slot-$s.cnf" "$source_dir/replay/slot-$s.drat" \
         -l "$dest/certificates/slot-$s.drat" -q > "$dest/logs/slot-$s.trim.log" 2>&1
    grep -q -a 's VERIFIED' "$dest/logs/slot-$s.trim.log"
    "$P" "$source_dir/slot-$s.cnf" "$dest/certificates/slot-$s.drat" -q \
         > "$dest/logs/slot-$s.replay.log" 2>&1
    grep -q -a 's VERIFIED' "$dest/logs/slot-$s.replay.log"
    printf 'slot-%s trimmed and independently replayed\n' "$s"
done
