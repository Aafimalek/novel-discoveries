#!/usr/bin/env python3
"""Check the exact two-line C10 LRAT prefix and its three input clauses only."""
from pathlib import Path
import json, sys
cert=Path(sys.argv[1])
with (cert/'core.lrat').open('rb') as f:
    opened, first=f.readline(),f.readline()
drow=opened.split()
assert drow[:2]==[b'14664',b'd'] and drow[-1]==b'0'
deleted=set(map(int,drow[2:-1]))
tokens=list(map(int,first.split()))
at=tokens.index(0)
n,learned,hints=tokens[0],tokens[1:at],tokens[at+1:-1]
assert n==15051 and learned==[1298,1299,1300,1301,1302,-9721]
assert hints==[12732,50,12733] and tokens[-1]==0
assert not (deleted & set(hints))
input={}
with (cert/'core.cnf').open('rb') as cnf:
    assert cnf.readline().split()==[b'p',b'cnf',b'11558',b'14664']
    for k,row in enumerate(cnf,1):
        if k in hints:
            tok=list(map(int,row.split()))
            assert tok[-1]==0 and 0 not in tok[:-1]
            input[k]=tok[:-1]
        if k==max(hints):break
expected={12732:[1],50:[-1,1297],12733:[-1297,1298,1299,1300,1301,1302,-9721]}
assert input==expected
falsified=set(learned)
units=[]
for k in hints[:-1]:
    remaining=[s for s in input[k] if s not in falsified]
    assert len(remaining)==1,(k,remaining)
    units.append(remaining[0])
    falsified.add(-remaining[0])
assert all(x in falsified for x in input[hints[-1]])
print(json.dumps(dict(row=n,target=learned,hints=hints,inputs=input,
    units=units,conflict=hints[-1],opening_deleted=len(deleted),
    bytes_consumed_from_lrat=len(opened)+len(first),core_rows_scanned=max(hints)),indent=2))
