#!/usr/bin/env python3
"""Emit bounded Init-only arithmetic checks over the published graph."""
from pathlib import Path
opts='set_option maxRecDepth 32768\nset_option maxHeartbeats 160000000\n'
head='import RotationArithmetic\n\nnamespace CertifiedG449Rotation\nopen G449OrbitArithmetic\n'+opts+'\n'
names=[]
for n in range(28):
    s=f'EdgeData{n:02d}'
    path=f'RotEdge{n:02d}'
    t=f'rotEdge{n:02d}_checked'
    names.append((path,t))
    Path(path+'.lean').write_text(head+
        f'theorem {t} : {s}.all edgeActionValid = true := by decide +kernel\n'+
        f'#print axioms {t}\nend CertifiedG449Rotation\n')
h=''.join(f'import {m}\n' for m,t in names)
p='''namespace CertifiedG449Rotation
open G449OrbitArithmetic
'''+opts+'''
theorem checked_rotation_of_published_edges :
    allPublishedEdges.all edgeActionValid = true := by
  simp only [allPublishedEdges,List.all_append,
    '''+', '.join(t for m,t in names)+''', Bool.and_self]

#print axioms checked_rotation_of_published_edges
end CertifiedG449Rotation
'''
Path('AllRotatedEdges.lean').write_text(h+'\n'+p)
