"""Independently validate both positive controls, including the shorter cup ban."""
from itertools import combinations
from pathlib import Path
import sys
if len(sys.argv) != 2:
    raise SystemExit("usage: python3 check_positive.py path/to/endpoint-benchmark")
sys.path.insert(0, str(Path(sys.argv[1]).resolve()))
from check_models import check
for k, n in [(5,7),(6,15)]:
    name = f'anchor-{k}-{n}'
    sign = check(f'{name}.cnf', f'{name}.log', n, k)
    num = 0
    for xs in combinations(range(n), k-1):
        assert not all(sign[t] for t in combinations(xs,3)), xs
        num += 1
    print(f'{name}: checked {num} shorter positive-chain candidates')
