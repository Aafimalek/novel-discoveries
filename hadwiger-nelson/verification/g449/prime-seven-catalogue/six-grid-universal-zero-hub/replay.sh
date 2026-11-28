#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -ne 7 ]; then
  printf '%s\n' "usage: $0 PINNED_DIR CATALOGUE SINGLE TRIPLE FOUR FIVE FRESH_RUN_DIR" >&2
  exit 2
fi
here=$(cd -- "$(dirname -- "$0")" && pwd)
original=$(realpath -- "$1")
catalogue=$(realpath -- "$2")
single=$(realpath -- "$3")
triple=$(realpath -- "$4")
four=$(realpath -- "$5")
five=$(realpath -- "$6")
work=$(realpath -m -- "$7")
mkdir -- "$work"
cd -- "$work"
ulimit -v 132000
export OPENBLAS_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
pin() {
  local pin name
  name=$1
  pin=$(awk -v n="$name" '$2==n {print $1}' "$here/INPUTS.sha256")
  [ "${#pin}" -eq 64 ]
  printf '%s  %s\n' "$pin" "$2" | sha256sum -c -
}
pin G449.k21 "$original/G449.k21"
pin G449.s6 "$original/G449.s6"
pin denominator-seven-directions.tsv "$catalogue"
pin extension-witnesses.json "$single"
pin triple-residual-witness.json "$triple"
pin four-witness.json "$four"
pin five-witness.json "$five"
timeout 25s python3 "$here/prepare.py" "$original" "$catalogue" "$single" work.txt "$triple" "$four" "$five" > prepare.log
pin work.txt work.txt
timeout 25s "${CXX:-g++}" -std=c++20 -O2 --param=ggc-min-expand=1 --param=ggc-min-heapsize=1024 "$here/zero_hub.cpp" -o zero_hub
for h in $(seq 0 31); do
  timeout 25s ./zero_hub work.txt "${h}.residual" "$h" 32 1000000 >"${h}.log"
  if [ -s "${h}.residual" ]; then
    printf 'Stopped at shard %s: unexpected bank residual.\n' "$h" >&2
    exit 8
  fi
done
pin work.txt work.txt
python3 "$here/collect.py" . 32 --expect-closed | tee summary.log
