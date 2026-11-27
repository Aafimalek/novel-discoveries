#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
L="${LEAN:-lean}"
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"

# Obtain replay.py and the hash-pinned data as described in the previous pilot.
python3 replay.py --sparse6 G449.s6 --cnf replay-base.cnf --edges-json edges.json
python3 gen_slim_data.py
python3 gen_slim_edges.py
for module in OrbitArithmetic SlimG449Data OrbitCheck AllRoots OrbitTransport EdgeArithmetic SlimG449Vertices; do
    "$L" -o "$module.olean" "$module.lean"
done
for file in DirBlock[0-9].lean; do
    "$L" -o "${file%.lean}.olean" "$file"
done
"$L" -o AllNormsScan.olean AllNormsScan.lean
for file in EdgeData[0-9][0-9].lean; do
    "$L" -o "${file%.lean}.olean" "$file"
done
for module in AllPublishedEdges LinkedNorms FourColourCNF G449Formula; do
    "$L" -o "$module.olean" "$module.lean"
done
"$L" --run DumpG449CNF.lean > lean-base.cnf
cmp lean-base.cnf replay-base.cnf
sha256sum lean-base.cnf
