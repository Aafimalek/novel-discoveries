#!/usr/bin/env python3
"""Verify the frozen 24-row fixture against the exact external file slice."""
from pathlib import Path
import itertools,re,sys
p=Path(sys.argv[1]); canonical=Path(__file__).with_name('first-four-packets.rows')
lo,hi=258385,258408 # 1-based body rows, not including the header
with p.open('rb') as f:
    assert f.readline()==b'p cnf 37365 474144\n'
    chunk=b''.join(itertools.islice(f,lo-1,hi))
assert chunk==canonical.read_bytes()
raw=chunk.splitlines()
assert len(raw)==24 and all(re.fullmatch(rb'(?:-?[1-9][0-9]* ){3}0',r) for r in raw)
rows=[tuple(int(x) for x in line.split()[:-1]) for line in raw]
assert all(0<abs(l)<=37365 for r in rows for l in r)
print(f'Exact clause body rows {lo}–{hi}: {len(rows)} rows, {len(chunk)} bytes')
