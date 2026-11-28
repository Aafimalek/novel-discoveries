#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
lean="${LEAN:-lean}"
measure() {
  python3 measure.py timeout --kill-after=3 30 "$lean" -j1 -M "${LEAN_MEMORY_MB:-960}" -R "$PWD" "$@"
}
for stem in ConwayGuyNineNat ConwayGuyNine; do
  f="NineSeparatedSubsetSums/$stem"
  measure -o "$f.olean" "$f.lean"
done
measure Audit.lean
