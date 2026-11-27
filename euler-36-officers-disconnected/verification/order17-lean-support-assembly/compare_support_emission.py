from pathlib import Path
from ast import literal_eval
from hashlib import sha256
import sys
C=[tuple(row) for row in literal_eval(Path(sys.argv[1]).read_text())]
assert len(C)==31752
for filename in sys.argv[2:]:
    data=Path(filename).read_bytes()
    got=[tuple(map(int,row.split()[:-1])) for row in data.splitlines()[1:1+31752]]
    assert C==got,(filename,next((i+1,x,y) for i,(x,y) in enumerate(zip(C,got)) if x!=y))
    print(filename,sha256(data).hexdigest(),'exact Lean-emitted prefix 1..31752')
