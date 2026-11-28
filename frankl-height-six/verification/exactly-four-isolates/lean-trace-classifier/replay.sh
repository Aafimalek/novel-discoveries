#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN_PATH:?Set LEAN_PATH to the pinned Mathlib library paths}"
export LEAN_PATH="$PWD:$LEAN_PATH"
LEAN="${LEAN:-lean}"
for name in FranklFourTraceCertificateDefinitions FranklFourTraceCertificates; do
  timeout --kill-after=5s 205s "$LEAN" -j1 -M2500 -R "$PWD" -o "$name.olean" "$name.lean"
done
