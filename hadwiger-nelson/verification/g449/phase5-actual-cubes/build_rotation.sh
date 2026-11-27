#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
if [ "$#" -lt 2 ] || [ "$#" -gt 3 ]; then
  echo "usage: $0 <hash-pinned input directory> <compiled phase3 Lean modules> [compiled finite-coverage module directory]" >&2
  exit 2
fi
L="${LEAN:-lean}"
export LEAN_PATH="$PWD:$2${3:+:$3}${LEAN_PATH:+:$LEAN_PATH}"
python3 generate_rotation.py "$1"
python3 gen_checks.py
for m in RotationData RotationArithmetic CentralChecks GeomNumeric; do
  "$L" -o "$m.olean" "$m.lean"
done
for f in RotEdge[0-9][0-9].lean; do
  "$L" -o "${f%.lean}.olean" "$f"
done
for m in AllRotatedEdges RotationAutomorphism RotationPowers; do
  "$L" -o "$m.olean" "$m.lean"
done

if [ "$#" -eq 3 ]; then
  for m in WordCoding NormalizeColour TypedCubes BaseCubeLift; do
    "$L" -o "$m.olean" "$m.lean"
  done
fi
