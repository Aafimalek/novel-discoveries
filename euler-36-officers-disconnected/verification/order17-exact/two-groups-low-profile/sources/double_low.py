"""Specialize a normalized size-17 double-overlap case by low-group position."""
import sys
from pathlib import Path
from itertools import combinations
origin = Path(__file__).with_name("min2_f17.py")
case, axis, path = sys.argv[1:]
axis = int(axis)
assert case in {"double-same","double-cross1","double-cross2"} and 0<=axis<4
code=origin.read_text().split("\nF.to_file(",1)[0]
sys.argv=[str(origin),case,path]
scope={}
exec(compile(code,str(origin),"exec"),scope)
F,D=scope["F"],scope["D"]
# If axis is a candidate side, labels 3,4,5 are already known high.
if axis>=2:
    for a in range(3):
        F.append([-D[axis,a][3]])
else:
    for labels in combinations(range(6),4):
        F.append([-D[axis,a][3] for a in labels])
F.to_file(path)
print(case,axis,F.nv,len(F.clauses))
