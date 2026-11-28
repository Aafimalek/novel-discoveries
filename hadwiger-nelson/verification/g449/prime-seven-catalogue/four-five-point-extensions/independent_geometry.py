#!/usr/bin/env python3
"""Reconstruct the union graph directly by exact Laurent polynomial reduction."""
import hashlib,json
import sys
from itertools import combinations
from pathlib import Path
from audit_layers import PINNED,parse_sparse6,sub
from independent_triple_audit import exact_norm

base=Path(sys.argv[1])
W=json.loads(Path(sys.argv[2]).read_text())
K=(base/"G449.k21").read_bytes()
S=(base/"G449.s6").read_bytes()
assert hashlib.sha256(K).hexdigest()==PINNED["G449.k21"]
assert hashlib.sha256(S).hexdigest()==PINNED["G449.s6"]
_,rows=K.decode("ascii").splitlines()[0],K.decode("ascii").splitlines()[1:]
raw=[tuple(map(int,line.split())) for line in rows if line.strip()]
assert all(len(r)==13 and all(q%7==0 for q in r[:-1]) for r in raw)
pts=[tuple(q//7 for q in r[:-1]) for r in raw] + list(map(tuple,W["points"]))
n,base_edges=parse_sparse6(S)
assert n==449 and len(pts)==len(set(pts))==W["vertices"]==735
colors=W["colors"]
assert len(colors)==len(pts) and set(colors)==set("01234")
unit=(49,)+(0,)*11
old=set()
edges=0
known={}
for i,j in combinations(range(len(pts)),2):
    d=sub(pts[i],pts[j])
    if next(x for x in d if x)<0:
        d=tuple(-x for x in d)
    result=known.get(d)
    if result is None:
        result=known[d]=exact_norm(d)==unit
    if result:
        edges+=1
        if j<449:old.add((i,j))
        assert colors[i]!=colors[j],(i,j)
assert old==base_edges and edges==W["edges"]==4107
print("Independent Laurent geometry: 269,745 exact distance comparisons,",
      f"{len(known):,} distinct differences, 4,107 induced edges; every edge is properly colored.")
