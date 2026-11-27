"""Compare every min-one degree-one rectangle cut to the generated exact archive."""
from pathlib import Path
import sys,hashlib
block=Path(sys.argv[1]).read_bytes().splitlines()
assert len(block)==216
for filename in sys.argv[2:]:
    data=Path(filename).read_bytes()
    _,*clauses=data.splitlines()
    start=[i for i,x in enumerate(clauses) if x==block[0]]
    matches=[i for i in start if clauses[i:i+216]==block]
    assert len(matches)==1,(filename,matches)
    i=matches[0]
    print(f"{Path(filename).name}: {len(block)} exact rectangle clauses ({i+1}..{i+len(block)}), SHA-256 {hashlib.sha256(data).hexdigest()}")
