#!/usr/bin/env python3
"""Match candidate pin blocks against exact original archived CNF clauses."""
import ast, hashlib, json, subprocess, sys, tempfile
from pathlib import Path

emitted, archive = map(Path,sys.argv[1:])
raw_lines = emitted.read_text().splitlines()
anchors = ast.literal_eval(raw_lines[0])
blocks = {tuple(ast.literal_eval(ds)):ast.literal_eval(cs)
          for ds,cs in zip(raw_lines[1::2],raw_lines[2::2])}
assert len(blocks)==17 and len(anchors)==2
for meta in json.loads((archive/"manifest.json").read_text()):
    digits = tuple(map(int,meta["pinned_words"]))
    block = blocks.pop(digits)
    assert len(block)==28
    with tempfile.TemporaryDirectory() as tmp:
        path=Path(tmp)/"original.cnf"
        subprocess.run([sys.executable,str(archive/"generate.py"),meta["case"],str(path)],
                       stdout=subprocess.DEVNULL,check=True)
        src=path.read_bytes()
        assert hashlib.sha256(src).hexdigest()==meta["cnf_sha256"]
        c=[list(map(int,row.split()[:-1])) for row in src.splitlines()
           if row and row[:1] not in b"cp"]
        assert c[33044:33046]==anchors
        matches=[i+1 for i in range(len(c)-len(block)+1)
                 if c[i]==block[0] and c[i:i+len(block)]==block]
        assert len(matches)==1, (meta["case"],matches)
        print(f"{meta['case']}: exact anchors 33045–33046; pin/profile {matches[0]}–{matches[0]+27}")
assert not blocks
