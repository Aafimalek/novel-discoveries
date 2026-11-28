#!/usr/bin/env bash
set -euo pipefail
unset PYTHONOPTIMIZE
if [[ $# != 1 ]]; then
  echo "Usage: bash replay.sh INPUT_DIR (containing the pinned G449.s6 and G449.k21)" >&2
  exit 64
fi
input="$(cd "$1" && pwd)"
here="$(cd "$(dirname "$0")" && pwd)"
catdir="${G449_CATALOGUE_DIR:-$(cd "$here/.." && pwd)}"
export PYTHONPATH="$here:$catdir${PYTHONPATH:+:$PYTHONPATH}"
build="$(mktemp -d)"
trap 'rm -rf -- "$build"' EXIT
d="$catdir/denominator-seven-directions.tsv"
python3 "$here/prepare.py" "$input" "$d" "$catdir/extension-witnesses.json" "$catdir/triple-residual-witness.json" "$build"
"${CXX:-g++}" -std=c++20 -O2 -UNDEBUG -D_GLIBCXX_ASSERTIONS -Wall -Wextra -Wpedantic "$here/enumerate.cpp" -o "$build/enumerate"
"$build/enumerate" "$build/data.txt" "$build/residual.txt"
python3 "$here/finish.py" "$build/data.json" "$build/residual.txt" "$here/four-witness.json"
"${CXX:-g++}" -std=c++20 -O2 -UNDEBUG -D_GLIBCXX_ASSERTIONS -Wall -Wextra -Wpedantic "$here/independent_enumeration.cpp" -o "$build/independent-enumeration"
"$build/independent-enumeration" "$build/data.txt" "$build/residual.txt"
python3 "$here/independent_geometry.py" "$input" "$here/four-witness.json"
python3 "$here/classify_offgrid_four.py" "$input" "$d"
python3 "$here/one_base_high_pair.py" "$input" "$d"
