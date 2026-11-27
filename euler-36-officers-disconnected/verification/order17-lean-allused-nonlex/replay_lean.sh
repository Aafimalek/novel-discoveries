#!/bin/sh
set -eu
cd "$(dirname "$0")"
repo="$PWD"
LEAN_BIN=${LEAN_BIN:-lean}
export LEAN_PATH="$repo/lean-source-closure${LEAN_PATH:+:$LEAN_PATH}"
(
  cd lean-source-closure
  sha256sum -c ../lean-source-sha256.txt
  while IFS= read -r module; do
    stem=$(printf '%s' "$module" | tr . /)
    "$LEAN_BIN" -j1 -o "$stem.olean" "$stem.lean"
  done < ../local-build-order.txt
)
