#!/usr/bin/env python3
"""Audit every signed clause of the candidate rectangle run in the exact archives."""
import ast, hashlib, json, subprocess, sys, tempfile
from pathlib import Path

emitted, archive = map(Path,sys.argv[1:])
block = [ast.literal_eval(row) for row in emitted.read_text().splitlines()]
assert len(block) == 15552 and all(len(c)==8 for c in block)
for meta in json.loads((archive/"manifest.json").read_text()):
    with tempfile.TemporaryDirectory() as tmp:
        path=Path(tmp)/"original.cnf"
        subprocess.run([sys.executable,str(archive/"generate.py"),meta["case"],str(path)],
                       stdout=subprocess.DEVNULL,check=True)
        src=path.read_bytes()
        assert hashlib.sha256(src).hexdigest() == meta["cnf_sha256"]
        cs=[list(map(int,row.split()[:-1])) for row in src.splitlines()
            if row and row[:1] not in b"cp"]
        starts=[i+1 for i,c in enumerate(cs) if c==block[0] and cs[i:i+len(block)] == block]
        assert len(starts)==1, (meta["case"],starts)
        print(f"{meta['case']}: clauses {starts[0]}–{starts[0]+len(block)-1}; {len(block)} exact signed clauses")
