#!/usr/bin/env bash
# Usage: check.sh /path/to/lean /path/to/EndpointGuardCore.lean generated_dir [pinned_upstream_checkout]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
LEAN="$1"
CORE="$2"
OUT="$3"
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"
unset PYTHONOPTIMIZE
(cd "$HERE" && sha256sum -c SOURCE.sha256)
"$LEAN" --root="$(dirname "$CORE")" -o "$OUT/EndpointGuardCore.olean" "$CORE"
(
  cd "$HERE"
  LEAN_PATH="$OUT" "$LEAN" -o "$OUT/NumberedCNF.olean" NumberedCNF.lean
  LEAN_PATH="$OUT" "$LEAN" -o "$OUT/EndpointBaseAliases.olean" EndpointBaseAliases.lean
  LEAN_PATH="$OUT" "$LEAN" -o "$OUT/NumberedAudit.olean" NumberedAudit.lean
)
extra=()
if [ "$#" -eq 4 ]; then
    UPSTREAM="$(cd "$4" && pwd)"
    export PYTHONPATH="$UPSTREAM${PYTHONPATH:+:$PYTHONPATH}"
    (cd "$UPSTREAM" && sha256sum -c "$HERE/upstream.sha256")
    extra+=(--compare-upstream)
fi
python3 "$HERE/endpoint_dimacs.py" 9 5 5 5 "$OUT/es9.cnf" "${extra[@]}"
python3 "$HERE/endpoint_dimacs.py" 32 7 7 6 "$OUT/es32-anchor.cnf" "${extra[@]}"
python3 "$HERE/endpoint_dimacs.py" 33 7 7 7 "$OUT/es33-unanchored.cnf" "${extra[@]}"
(cd "$OUT" && sha256sum -c "$HERE/generated.sha256")
