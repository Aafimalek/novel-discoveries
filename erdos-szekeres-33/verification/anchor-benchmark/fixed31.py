"""Use an exact angular reordering of the known 32-point geometric witness."""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import subprocess
import sys

if len(sys.argv) != 3:
    raise SystemExit("usage: python3 fixed31.py path/to/endpoint-benchmark /path/to/kissat")
src = Path(sys.argv[1]).resolve()
sys.path[:0] = [str(src/'upstream'), str(src)]
from lib.erdos import etv_signotope
from check_models import check
from extension32 import lower_witness, determinant

orig = sorted(lower_witness())
root = orig[0]
key = lambda q: Fraction(q[1]-root[1], q[0]-root[0])
points = sorted(orig[1:], key=key)
assert len(points) == 31
assert all(determinant(root, p, q)>0 for p,q in combinations(points,2))
wanted = {}
X=etv_signotope(7,7,6,len(points))
for t in combinations(range(len(points)),3):
    area = determinant(*(points[i] for i in t))
    assert area, t
    wanted[t] = area>0
    X.add(X.v[t] if area>0 else ~X.v[t])
name='anchor-7-fixed31'
X.write(name+'.cnf')
with open(name+'.log','wb') as out:
    rc = subprocess.run([sys.argv[2],name+'.cnf'],stdout=out,stderr=out,timeout=30).returncode
assert rc == 10, rc
sign = check(name+'.cnf',name+'.log',len(points),7)
assert sign == wanted
for t in combinations(range(len(points)),6):
    assert not all(sign[u] for u in combinations(t,3)), t
print('All 4,495 fixed orientation signs match; no positive six-set.')
