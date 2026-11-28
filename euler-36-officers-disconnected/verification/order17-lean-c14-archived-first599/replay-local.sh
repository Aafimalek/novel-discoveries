#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN_BIN:?Pin absolute Lean 4.36 binary}"
: "${LEAN_C14_DEP_PATH:?Set colon-separated proof/project olean paths through exactArchiveThrough9423 plus Mathlib}"
export LEAN_PATH="$PWD:$PWD/generated:$LEAN_C14_DEP_PATH"
mkdir -p "$PWD/tmp"
export TMPDIR="$PWD/tmp"
while IFS= read -r m; do
  src="$PWD/generated/$m.lean"; [[ -f $src ]] || src="$PWD/$m.lean"
  root=$(dirname "$src")
  timeout 17 "$LEAN_BIN" -j1 -M2450 -DwarningAsError=true -R "$root" -o "$root/$m.olean" "$src"
done < checked-order.txt
