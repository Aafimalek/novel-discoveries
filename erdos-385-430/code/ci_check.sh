#!/bin/bash
# Rebuild the search program, recompute every exception below 10^7, and compare
# with the committed list. Also cross-check the definitions by brute force.
set -euo pipefail
cd "$(dirname "$0")"
gcc -O2 -fopenmp -o f385 f385.c -lm
./f385 4 10000001 > out_1e7.txt
grep '^BAD ' out_1e7.txt | awk '$2 >= 5 {print $2}' > got.txt
tr -d '\r' < ../data/exceptions.txt | awk '$1 < 10000001' > want.txt
diff want.txt got.txt
echo "exceptions below 10^7 match ($(wc -l < got.txt) values)"
python3 brute.py 3000 > brute.txt
grep -q '^agree True' brute.txt
echo "brute-force definitions agree for n <= 3000"
