#!/usr/bin/env python3
"""Generate numeric Lean certificates, not upstream artifacts."""
from pathlib import Path
import hashlib
import json
from replay import EXPECTED_FILE_SHA256, rem42

data=Path('G449.k21').read_bytes()
assert hashlib.sha256(data).hexdigest()==EXPECTED_FILE_SHA256
raw=[tuple(map(int,x.split()))[:12] for x in data.decode('ascii').splitlines()[1:]]
edges=json.loads(Path('edges.json').read_text())
dlist=[]
for a,b in edges:
    v=tuple(x-y for x,y in zip(raw[a],raw[b]))
    d=min(v,tuple(-x for x in v))
    if d not in dlist:dlist.append(d)
assert len(dlist)==49
parent=[None]*49
roots=[]
ms=set(range(49))
while ms:
    r=min(ms)
    roots.append(r)
    parent[r]=(r,0,False)
    ms.remove(r)
    prev=r
    for k in range(1,7):
        shown=rem42([0]*6+list(dlist[prev]))
        canon=min(shown,tuple(-x for x in shown))
        i=dlist.index(canon)
        ms.remove(i)
        parent[i]=(prev,k,canon!=shown)
        prev=i
assert roots==[0,1,3,4,9,14,31]

def vec(v): return '['+', '.join(map(str,v))+']'
def table(v): return '[\n'+',\n'.join('  '+vec(x) for x in v)+']'
powers=[rem42([0]*x+[1]) for x in range(54)]
p='''import OrbitArithmetic

namespace G449OrbitArithmetic

def rawDirections : List (List Int) := '''+table(dlist)+'''
def powersTable : List (List Int) := '''+table(powers)+'''
def dirs (k i : Nat) : Int := (rawDirections.getD k []).getD i 0
def powers (k i : Nat) : Int := (powersTable.getD k []).getD i 0
def parentTable : List Step := [
'''+',\n'.join(f'  ⟨{prev},{k},{str(f).lower()}⟩' for prev,k,f in parent)+''']
def parent (k : Nat) : Step := parentTable.getD k ⟨0,0,false⟩
def roots : List Nat := '''+vec(roots)+'''

end G449OrbitArithmetic
'''
Path('SlimG449Data.lean').write_text(p)
