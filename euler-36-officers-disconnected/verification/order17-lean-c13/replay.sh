#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export LEAN_PATH=".${LEAN_PATH:+:$LEAN_PATH}"
for f in FactoredDriver ContainmentDriver C13CoreSorted C13FullSorted; do
  "${LEAN:-lean}" -j1 -R . -o "EulerBatch/$f.olean" "EulerBatch/$f.lean"
done
