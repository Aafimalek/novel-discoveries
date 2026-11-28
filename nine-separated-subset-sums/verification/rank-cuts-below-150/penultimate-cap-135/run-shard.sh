#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
test -n "${1:-}"
exec 9>/tmp/nine149-rank-run135-slot.lock
flock -n 9 || { echo 'A cap-135 worker already holds the local slot'; exit 75; }
mkdir -p logs
case "$1" in
    freeze|check|replay)
        log="logs/phase2-$1-$(date +%s)-$$.log"
        (ulimit -v 143000; timeout --kill-after=2 35 python3 -u checkpoint.py "$@") 2>&1 | tee "$log"
        ;;
    *)
        log="logs/$1-$(date +%s)-$$.log"
        (ulimit -v 143000; timeout --kill-after=2 35 python3 -u refine_shard.py "$@") 2>&1 | tee "$log"
        ;;
esac
