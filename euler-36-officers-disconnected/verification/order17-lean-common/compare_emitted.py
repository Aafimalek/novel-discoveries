from pathlib import Path
from ast import literal_eval
from hashlib import sha256
import sys
R=[tuple(row) for row in literal_eval(Path(sys.argv[1]).read_text())]
P,E=R[:1292],R[1292:]
assert len(P)==1292 and len(E)==1520
for path in map(Path,sys.argv[2:]):
    data=path.read_bytes()
    rows=[tuple(map(int,line.split()[:-1])) for line in data.splitlines()[1:]]
    assert rows[31752:33044]==P
    positions=[i for i,c in enumerate(rows) if c==E[0] and rows[i:i+len(E)]==E]
    assert len(positions)==1
    i=positions[0]
    print(f'{path}: {sha256(data).hexdigest()} exact Lean-emitted 2812, offsets 31753..33044 and {i+1}..{i+len(E)}')
