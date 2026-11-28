#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_PATH="$PWD:${LEAN_PATH:?Use only pinned Mathlib and package objects}"
LEAN_BIN="${LEAN_BIN:-lean}"
for module in PlanarPrelude QuadrupleReduction TriangleOrientation QuadrupleParity OrientationClauses Signotope FullReduction; do
    "$LEAN_BIN" -j1 -M2400 -DwarningAsError=true -o "ES33/$module.olean" "ES33/$module.lean"
done
