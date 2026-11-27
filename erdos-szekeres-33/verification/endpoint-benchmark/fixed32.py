#!/usr/bin/env python3
"""Use the upstream DP to check the fixed integer witness, not a 33-point solve."""
from itertools import combinations
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).parent / "upstream"))
from lib.erdos import etv_signotope
from check_models import check
from extension32 import lower_witness, determinant

P = lower_witness()
X = etv_signotope(7,7,7,32)
wanted = {}
for t in combinations(range(32),3):
    area = determinant(*(P[i] for i in t))
    assert area != 0
    wanted[t] = area>0
    X.add(X.v[t] if area>0 else ~X.v[t])
X.write('dp-fixed-32-7.cnf')
print('fixed 32 vars clauses',X._num_vars,len(X._clauses))
if len(sys.argv) > 1:
    sign = check('dp-fixed-32-7.cnf',sys.argv[1],32,7)
    assert sign == wanted
    print('all 4,960 fixed orientations matched')
