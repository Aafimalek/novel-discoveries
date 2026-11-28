#!/usr/bin/env bash
# Usage: check.sh /path/to/lean /path/to/NumberedCNF.lean /path/to/output
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
LEAN="$(realpath "$1")"
DEP="$(realpath "$2")"
mkdir -p "$3"
OUT="$(cd "$3" && pwd)"
(
  cd "$HERE"
  sha256sum -c SOURCE.sha256
)
echo "$(cat "$HERE/dependency.sha256")  $DEP" | sha256sum -c -
"$LEAN" --version
FLAGS=(-j 1 -M 2100 -DwarningAsError=true)
timeout 55 "$LEAN" "${FLAGS[@]}" --root="$(dirname "$DEP")" -o "$OUT/NumberedCNF.olean" "$DEP"
(
  cd "$HERE"
  export LEAN_PATH="$OUT"
  timeout 40 "$LEAN" "${FLAGS[@]}" -o "$OUT/NumberedMatches.olean" NumberedMatches.lean
  timeout 40 "$LEAN" "${FLAGS[@]}" -o "$OUT/ReflectionLexTransport.olean" ReflectionLexTransport.lean
)
