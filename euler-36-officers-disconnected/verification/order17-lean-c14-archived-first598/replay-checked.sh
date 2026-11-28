#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN_BIN:?Set absolute pinned Lean 4.36 binary}"
: "${GLOBAL_C14_DIR:?Set built c14-global-first48 directory}"
: "${ORIGINAL_C14_DIR:?Set built c14-exact-global-first72 directory}"
: "${THROUGH9113_C14_DIR:?Set built c14-exact-through9113 directory}"
: "${THROUGH9278_C14_DIR:?Set built c14-exact-through9278 directory}"
: "${THROUGH9373_C14_DIR:?Set built c14-exact-through9373 directory}"
: "${THROUGH9410_C14_DIR:?Set built c14-exact-through9410 directory}"
: "${LEAN_MATHLIB_PATH:?Set colon-separated pinned dependency olean roots}"
export LEAN_PATH="$PWD/generated:$THROUGH9410_C14_DIR/generated:$THROUGH9373_C14_DIR/generated:$THROUGH9278_C14_DIR/generated:$THROUGH9113_C14_DIR/generated:$ORIGINAL_C14_DIR:$GLOBAL_C14_DIR:$GLOBAL_C14_DIR/generated:$LEAN_MATHLIB_PATH"
mkdir -p "$PWD/tmp"
export TMPDIR="$PWD/tmp"
while IFS= read -r f; do
  timeout 73 "$LEAN_BIN" -j1 -M2450 -DwarningAsError=true -R "$PWD/generated" -o "$PWD/generated/$f.olean" "$PWD/generated/$f.lean"
done < checked-order.txt
