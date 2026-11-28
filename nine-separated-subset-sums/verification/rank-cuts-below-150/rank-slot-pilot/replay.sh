#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python3 central_root_lp.py central-root-farkas.json --verify-only
python3 central_matching.py --verify-only
python3 central_branch.py --verify-only
python3 rank_slot.py --verify-only
