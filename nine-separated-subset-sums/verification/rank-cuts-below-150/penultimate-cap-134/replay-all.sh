#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
dest="$(mktemp -d /tmp/cap134-independent.XXXXXX)"
cp -- anchored134.py cap127_safe.py cap_moment.py checkpoint.py orbit.py refine_shard.py run-shard.sh "$dest/"
cp -a checkpoint "$dest/"
cd "$dest"
reserve() {
    test "$(awk '/MemAvailable/{print $2}' /proc/meminfo)" -ge 1250000
    test "$(df -Pm /tmp | awk 'NR==2{print $4}')" -ge 420
}
reserve
./run-shard.sh replay
for id in $(python3 -c 'import json; print(*(x["id"] for x in json.load(open("checkpoint/manifest.json"))["shards"]))'); do
    reserve
    ./run-shard.sh "$id" --max-depth 4
done
./run-shard.sh status | tee "$dest/exact-result.log"
grep -Fx 'Cleared shards: 140 of 140' "$dest/exact-result.log"
echo "Independent guarded replay complete in $dest"
