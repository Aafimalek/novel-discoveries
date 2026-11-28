#!/usr/bin/env python3
"""Check that the staged pilot is the exact six-body-row slice of a file."""
from pathlib import Path
import itertools,re,sys
p=Path(sys.argv[1])
here=Path(__file__).resolve().parent
lo,hi=258385,258390 # 1-indexed CNF clauses, excluding header
with p.open('rb') as f:
    h=f.readline()
    assert h==b'p cnf 37365 474144\n'
    chunk=b''.join(itertools.islice(f,lo-1,hi))
assert chunk==(here/'first-packet.rows').read_bytes()
raw=chunk.splitlines()
assert len(raw)==6 and all(re.fullmatch(rb'(?:-?[1-9][0-9]* ){3}0',r) for r in raw)
rows=[tuple(int(x) for x in line.split()[:-1]) for line in raw]
assert all(0<abs(l)<=37365 for r in rows for l in r)
print(h.decode().strip(),lo,hi)
for r in rows: print(*r)
