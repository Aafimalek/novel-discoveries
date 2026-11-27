#!/usr/bin/env bash
# Run from a Lean 4.36.0 Lake project pinned to the Mathlib revision named in README.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
original="${1:?Usage: bash verify.sh path/to/generated/slot-32.cnf}"
temp="$(mktemp -d)"
trap 'rm -rf "$temp"' EXIT
cp "$original" "$temp/original.cnf"
cp "$HERE/Slot32Containment.lean" "$HERE/core.cnf" "$HERE/core.lrat" "$temp/"
(cd "$temp" && sha256sum -c "$HERE/SHA256SUMS")
if [ -z "${LEAN:-}" ]; then
  lake env lean "$temp/Slot32Containment.lean"
else
  "$LEAN" "$temp/Slot32Containment.lean"
fi
