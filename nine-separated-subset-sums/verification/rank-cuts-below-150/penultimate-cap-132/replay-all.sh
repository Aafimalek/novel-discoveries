#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
dest="$(mktemp -d "${TMPDIR:-/tmp}/cap132-independent.XXXXXX")"
reserve() {
    test "$(awk '/MemAvailable/{print $2}' /proc/meminfo)" -ge 1250000
    test "$(df -Pm /tmp | awk 'NR==2{print $4}')" -ge 420
}
reserve
./run-shard.sh replay
for id in $(python3 -c 'import json; print(*(x["id"] for x in json.load(open("checkpoint/manifest.json"))["shards"]))'); do
    reserve
    ./run-shard.sh "$id" --results "$dest" --max-depth 4
done
./run-shard.sh status --results "$dest" | tee "$dest/exact-result.log"
grep -Fx 'Cleared shards: 70 of 70' "$dest/exact-result.log"
echo "Independent guarded replay complete in $dest"
