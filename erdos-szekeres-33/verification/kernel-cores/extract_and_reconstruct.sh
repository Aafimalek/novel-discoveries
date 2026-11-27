#!/usr/bin/env bash
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
D="${1:?Need generated extension directory}"
D="$(cd "$D" && pwd)"
P="${DRAT_TRIM:?Need drat-trim}"
K="${KISSAT:?Need kissat}"
L="${LEAN:?Need lean with LEAN_PATH}"
export HERE D P K L
run_one(){
    local s="$1" wd="$HERE/slot-$1" rc=0 method=original
    mkdir -p "$wd"
    cd "$wd"
    local original="$D/slot-$s.cnf"
    local origproof="$D/certificates/slot-$s.drat"
    local leanname="Slot${s}Core.lean"
    local thm="slot${s}_core_unsat"
    if ! timeout -k 2 15 "$P" "$original" "$origproof" -c core.cnf -q >extract.log 2>&1 ||
       ! grep -a -q 's VERIFIED' extract.log ||
       ! python3 "$HERE/audit_core.py" "$original" core.cnf >containment.log 2>&1; then
        echo "$s extraction-failed"; return
    fi
    if ! timeout -k 2 10 "$P" core.cnf "$origproof" -U -L core.lrat -q >convert.log 2>&1 ||
       ! grep -a -q 's VERIFIED' convert.log; then
        method=plain
        timeout -k 2 25 "$K" --plain core.cnf plain.drat >solve.log 2>&1 || rc=$?
        if [ "$rc" != 20 ]; then echo "$s solver-failed-$rc"; return; fi
        if ! timeout -k 2 15 "$P" core.cnf plain.drat -U -L core.lrat -q >convert.log 2>&1 ||
           ! grep -a -q 's VERIFIED' convert.log; then
            echo "$s rup-convert-failed"; return
        fi
    fi
    cat > "$leanname" <<EOF_LEAN
import Mathlib.Tactic.Sat.FromLRAT

set_option maxHeartbeats 0
set_option maxRecDepth 100000

lrat_proof $thm (include_str "core.cnf") (include_str "core.lrat")

#print axioms $thm
EOF_LEAN
    rc=0
    timeout -k 3 45 "$L" -M 1600 "$wd/$leanname" >lean-kernel.log 2>&1 || rc=$?
    local nclauses
    nclauses=$(awk 'NR==1{print $4}' core.cnf)
    if [ "$rc" != 0 ] ||
       ! grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]" lean-kernel.log ||
       grep -q 'sorryAx\|native_decide' lean-kernel.log; then
        echo "$s lean-failed-$rc $method $nclauses"; return
    fi
    echo "$s VERIFIED $method $nclauses $(wc -c <core.lrat)"
}
export -f run_one
if [ "$#" -gt 1 ]; then shift; printf '%s\n' "$@"; else seq -w 0 32; fi |
    xargs -P2 -I{} bash -c 'run_one "$1"' _ {}
