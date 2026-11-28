#!/usr/bin/env bash
set -euo pipefail
unset PYTHONOPTIMIZE
if [[ $# != 1 ]]; then
  echo "Usage: bash replay.sh INPUT_DIR (containing the pinned G449.s6 and G449.k21)" >&2
  exit 64
fi
here="$(cd "$(dirname "$0")" && pwd)"
input="$(cd "$1" && pwd)"
old="${G449_CATALOGUE_DIR:-$(cd "$here/.." && pwd)}"
four="${G449_FOUR_DIR:-$old/four-five-point-extensions}"
export PYTHONPATH="$here:$old${PYTHONPATH:+:$PYTHONPATH}"
w="$(mktemp -d)"
trap 'rm -rf -- "$w"' EXIT
d="$old/denominator-seven-directions.tsv"
python3 "$here/hub_replay.py" "$input" "$d" "$old/extension-witnesses.json" --cross-check
python3 "$four/prepare.py" "$input" "$d" "$old/extension-witnesses.json" "$old/triple-residual-witness.json" "$w/inputs"
python3 "$here/translate.py" "$w/inputs/data.json" "$w/data37.txt" "$four/four-witness.json"
"${CXX:-g++}" -std=c++20 -O3 -UNDEBUG -D_GLIBCXX_ASSERTIONS "$here/enumerate5.cpp" -o "$w/enumerate5"
"$w/enumerate5" "$w/data37.txt" "$w/residual37.txt"
(cd "$w" && sha256sum --strict -c "$here/generated.sha256")
python3 "$here/finish.py" "$w/inputs/data.json" "$w/residual37.txt" "$here/five-witness.json"
"${CXX:-g++}" -std=c++20 -O3 -UNDEBUG -D_GLIBCXX_ASSERTIONS "$here/independent5.cpp" -o "$w/independent5"
"$w/independent5" "$w/data37.txt" "$w/residual37.txt"
python3 "$here/independent_geometry.py" "$input" "$here/five-witness.json"
