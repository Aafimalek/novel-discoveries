#!/usr/bin/env bash
# Run from the pinned Lean project's directory with Mathlib dependencies built.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
D="${1:?Path to the regenerated full extension DIMACS directory is required}"
D="$(cd "$D" && pwd)"
W="${2:-checked-lrat-cores}"
mkdir -p "$W"
W="$(cd "$W" && pwd)"
(cd "$HERE" && sha256sum -c ARCHIVE.sha256)
tar -xzf "$HERE/cores.tar.gz" -C "$W"
(cd "$W" && sha256sum -c "$HERE/CORE_FILES.sha256")
for slot in $(seq -w 0 32); do
    dir="$W/slot-$slot"
    python3 "$HERE/audit_core.py" "$D/slot-$slot.cnf" "$dir/core.cnf" >/dev/null
    if [ -z "${LEAN:-}" ]; then
        lake env lean "$dir/Slot${slot}Core.lean" > "$dir/fresh-axioms.log" 2>&1
    else
        "$LEAN" "$dir/Slot${slot}Core.lean" > "$dir/fresh-axioms.log" 2>&1
    fi
    grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$dir/fresh-axioms.log"
    ! grep -q 'sorryAx\|native_decide' "$dir/fresh-axioms.log"
    printf 'slot-%s kernel verified; original DIMACS subset checked independently\n' "$slot"
done
