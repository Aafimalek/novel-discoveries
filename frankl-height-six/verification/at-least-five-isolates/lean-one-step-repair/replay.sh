#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN_PATH:?Set LEAN_PATH to the pinned existing Frankl and Mathlib modules}"
export LEAN_PATH="$PWD:$LEAN_PATH"
LEAN="${LEAN:-lean}"
for part in Basic Height Application; do
  stem=FranklMissingDeletion$part
  timeout --kill-after=7 175 "$LEAN" -j1 -M2500 -R "$PWD" -o "$stem.olean" "$stem.lean"
done
