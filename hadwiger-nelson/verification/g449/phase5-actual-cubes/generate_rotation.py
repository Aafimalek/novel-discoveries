#!/usr/bin/env python3
"""Local-only Lean vertex-rotation data from the exact pinned G449 inputs."""
from pathlib import Path
from argparse import ArgumentParser
from hashlib import sha256
import json

coord_hash='58a45c4e653ff63e0218e1dec988e0a532905969dda3fc7bf84a3c83874a3848'
graph_hash='0db89dfb231a2722cb54a5bc3ce9e27afc672e73bd1230c41e08845b449e1b21'
edge_hash='0827ce02cc848fc0c8fbbaf6617bac07a30d91b1c3db522b311880e3135f0b01'
p=ArgumentParser()
p.add_argument("input",type=Path)
args=p.parse_args()
check=[(args.input/'G449.k21',coord_hash),(args.input/'G449.s6',graph_hash),(args.input/'edges.json',edge_hash)]
for path,d in check:
    assert sha256(path.read_bytes()).hexdigest()==d, f"unexpected {path.name} bytes"
lines=(args.input/'G449.k21').read_text().splitlines()
assert lines[0].split()==['K21','42','12','49','449']
points=[tuple(map(int,l.split()[:12])) for l in lines[1:]]
edges=[tuple(e) for e in json.loads((args.input/'edges.json').read_text())]
assert len(points)==len(set(points))==449 and edges==sorted(set(edges)) and len(edges)==2198
assert all(0<=i<j<449 for i,j in edges)

phi=(1,1,0,-1,-1,0,1,0,-1,-1,0,1,1)
def rho_pt(v):
    p=[0]*6+list(v)
    for i in range(17,11,-1):
        c=p[i]
        for j,b in enumerate(phi):p[i-12+j]-=c*b
    return tuple(p[:12])

def vec(v):return '['+', '.join(map(str,v))+']'
def br(r,offset=0):
    if len(r)==1: return str(r[0])
    m=len(r)//2
    return f'(if k < {offset+m} then {br(r[:m],offset)}\nelse {br(r[m:],offset+m)})'

pointid={v:i for i,v in enumerate(points)}
rot=[pointid[rho_pt(p)] for p in points]
assert len(set(rot))==449
inv=[None]*449
for i,j in enumerate(rot): inv[j]=i
center=pointid[(0,)*12]
assert rot[center]==center
edgeset=set(edges)
assert all(tuple(sorted((rot[i],rot[j]))) in edgeset for i,j in edges)
wheel={j for i,j in edges if i==center} | {i for i,j in edges if j==center}
assert len(wheel)==7
wheelC=[min(wheel)]
for _ in range(6):wheelC.append(rot[wheelC[-1]])
assert set(wheelC)==wheel and rot[wheelC[-1]]==wheelC[0]
assert all(tuple(sorted((i,j))) not in edgeset for i in wheel for j in wheel if i!=j)
rows=[[] for _ in points]
for a,b in edges:rows[a].append(b)

s='''import AllPublishedEdges

namespace CertifiedG449Rotation

open G449OrbitArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 50000000

def rot (k : Nat) : Nat :=
'''+br(rot)+'''

def inv (k : Nat) : Nat :=
'''+br(inv)+'''

def upperNeighbors (k : Nat) : List Nat :=
'''+br([vec(d) for d in rows])+f'''

def center : Nat := {center}
def ring : List Nat := {vec(wheelC)}

end CertifiedG449Rotation
'''
Path('RotationData.lean').write_text(s)
print('center',center,'neighbors in cyclic order',wheelC)
