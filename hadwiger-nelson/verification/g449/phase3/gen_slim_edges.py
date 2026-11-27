#!/usr/bin/env python3
"""Generate original arithmetic certificates for the pinned published edge list."""
import hashlib
import json
from pathlib import Path
from replay import EXPECTED_FILE_SHA256, read_sparse6
text=Path('G449.k21').read_bytes()
assert hashlib.sha256(text).hexdigest()==EXPECTED_FILE_SHA256
rows=[list(map(int,x.split())) for x in text.decode('ascii').splitlines()[1:]]
edges=[tuple(x) for x in json.loads(Path('edges.json').read_text())]
sparse6=Path('G449.s6')
assert hashlib.sha256(sparse6.read_bytes()).hexdigest()=='0db89dfb231a2722cb54a5bc3ce9e27afc672e73bd1230c41e08845b449e1b21'
n,listcheck=read_sparse6(sparse6)
assert n==449 and listcheck==edges and len(edges)==len(set(edges))==2198
dirs=[]
marked=[]
for a,b in edges:
    d=tuple(x-y for x,y in zip(rows[a][:12],rows[b][:12]))
    c=min(d,tuple(-x for x in d))
    if c not in dirs: dirs.append(c)
    marked.append(f'⟨{a},{b},{dirs.index(c)},{str(d!=c).lower()}⟩')
assert len(dirs)==49

def vec(xs): return '['+', '.join(map(str,xs))+']'
def lookup(items,offset=0):
    if len(items)==1:return items[0]
    m=len(items)//2
    return f'(if k<{offset+m} then {lookup(items[:m],offset)}\nelse {lookup(items[m:],offset+m)})'

want='''import EdgeArithmetic
import SlimG449Data

namespace G449OrbitArithmetic

set_option maxRecDepth 16384
set_option maxHeartbeats 30000000

def vertices (k : Nat) : Vertex :=
'''+lookup([f'⟨{vec(row[:12])},{row[12]}⟩' for row in rows])+'''

end G449OrbitArithmetic
'''
Path('SlimG449Vertices.lean').write_text(want)
check_names=[]
for s in range(0,len(marked),80):
    b=s//80
    selected=marked[s:s+80]
    name=f'EdgeData{b:02d}'
    check_names.append(name)
    module='''import SlimG449Vertices

namespace G449OrbitArithmetic
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000

def '''+name+''' : List Edge := [
'''+',\n'.join('  '+x for x in selected)+''']

theorem '''+name+'''_checked :
    '''+name+'''.all (Edge.validBool vertices dirs) = true := by decide +kernel

#print axioms '''+name+'''_checked
end G449OrbitArithmetic
'''
    Path(name+'.lean').write_text(module)

out=''.join(f'import {n}\n' for n in check_names)+'''
namespace G449OrbitArithmetic
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000

def allPublishedEdges : List Edge :=
  '''+' ++ '.join(check_names)+'''

theorem all_edge_links :
    allPublishedEdges.all (Edge.validBool vertices dirs) = true := by
  simp only [allPublishedEdges, List.all_append,
    '''+', '.join(n+'_checked' for n in check_names)+''', Bool.and_self]

theorem number_of_edges : allPublishedEdges.length = 2198 := by
  decide +kernel

theorem palette_five :
    (List.range 449).all (fun k => decide ((vertices k).colour < 5)) = true := by
  decide +kernel

#print axioms all_edge_links
#print axioms number_of_edges
#print axioms palette_five
end G449OrbitArithmetic
'''
Path('AllPublishedEdges.lean').write_text(out)
