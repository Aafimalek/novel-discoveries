"""Emit Lean literal data independently from the pinned G449 table."""
import hashlib
import json
from pathlib import Path
from replay import EXPECTED_FILE_SHA256, rem42

def vec(v):
    return '!['+', '.join(map(str,v))+']'

upstream=Path('G449.k21').read_bytes()
assert hashlib.sha256(upstream).hexdigest()==EXPECTED_FILE_SHA256
raw=[list(map(int,x.split())) for x in upstream.decode("ascii").splitlines()[1:]]
edges=json.loads(Path('edges.json').read_text())
powers=[rem42([0]*e+[1]) for e in range(54)]
dlist=[]
for a,b in edges:
    v=tuple(x-y for x,y in zip(raw[a],raw[b]))[:12]
    n=tuple(-x for x in v)
    d=min(v,n)
    if d not in dlist:dlist.append(d)
assert len(dlist)==49
nv='def table : Fin 54 → Coeff := ![\n'+',\n'.join('  '+vec(v) for v in powers)+']\n'
test='''set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
theorem table_checked : checkedPowers table := by
  unfold checkedPowers
  decide +kernel

def chosenDirections : Fin 49 → Coeff := ![
'''+',\n'.join('  '+vec(v) for v in dlist)+''']

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
theorem first_direction_checked : ∀ i, normCoeffs table (chosenDirections 0) i = (49^2 : ℤ) * start i := by
  decide +kernel

#print axioms table_checked
#print axioms first_direction_checked
'''
Path('G449Data.lean').write_text('import CyclotomicWitness\n\nnamespace PlaneColouring.Cyclotomic42\n\n'+nv+'\n'+test+'\nend PlaneColouring.Cyclotomic42\n')

samples=vec([vec(raw[i][:12]) for i in [0,1,8]])
Path('G449SampleRows.lean').write_text(
    'import G449Data\n\nnamespace PlaneColouring.Cyclotomic42\n'
    + 'def sampleRows : Fin 3 → Coeff := '+samples+'\n'
    + 'end PlaneColouring.Cyclotomic42\n')
