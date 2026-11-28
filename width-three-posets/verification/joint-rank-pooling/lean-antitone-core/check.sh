#!/usr/bin/env bash
set -euo pipefail
for source; do
  obj=$(basename "$source" .lean).olean
  timeout -k 1s 48s "$LEAN_BIN" -j1 -M650 -o "$obj" "$source" 2>&1 | tee "$(basename "$source" .lean).log"
  printf '%s exit=0\n' "$source" >> receipts.log
done
