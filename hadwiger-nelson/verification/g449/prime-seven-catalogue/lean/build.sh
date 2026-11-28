#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
L="${LEAN:-lean}"
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
for module in Mod7Trace Residue7 CoeffPoly ResidueTorus Mod7Witness Mod7Factor; do
  "$L" -j 1 -M 1600 -o "$module.olean" "$module.lean"
done
