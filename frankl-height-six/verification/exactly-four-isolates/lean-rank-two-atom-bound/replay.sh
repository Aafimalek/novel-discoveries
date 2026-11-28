#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export LEAN_PATH="$PWD:${LEAN_PATH:?Set LEAN_PATH to pinned built Mathlib}"
LEAN_BIN="${LEAN_BIN:-lean}"
for m in FranklHeightThreeSauer FranklRankTwoAtomGeometry FranklRankTwoAtomCounting FranklRankTwoPairSaturation; do
  "$LEAN_BIN" -j1 -M2500 -o "$m.olean" "$m.lean"
done
