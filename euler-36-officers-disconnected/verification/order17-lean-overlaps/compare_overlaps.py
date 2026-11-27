#!/usr/bin/env python3
"""Hash-check archived CNFs and compare every member to the corresponding exact Lean block."""
import ast, json, hashlib, subprocess, sys, tempfile
from pathlib import Path

family = [
    ("two-neighbors-one-group", "q2"),
    ("two-groups-high-profile", "double"),
    ("two-groups-low-profile", "double"),
    ("single-overlap", "one"),
    ("zero-overlap", "zero"),
]
emitted, archive = map(Path, sys.argv[1:])
blocks = {}
for s in emitted.read_text().splitlines():
    if not s.startswith("["):
        tag = s.rsplit(".",1)[-1]
        assert tag not in blocks and tag in {k for _, k in family}, s
        blocks[tag] = []
    else:
        blocks[tag].append(ast.literal_eval(s))

for subfolder, tag in family:
    d = archive / subfolder
    for item in json.loads((d/"manifest.json").read_text()):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)/"case.cnf"
            subprocess.run([sys.executable, str(d/"generate.py"),item["case"],str(out)], check=True,
                           stdout=subprocess.DEVNULL)
            raw = out.read_bytes()
            assert hashlib.sha256(raw).hexdigest() == item["cnf_sha256"]
            cnf = [list(map(int,ln.split()[:-1])) for ln in raw.splitlines() if ln and ln[:1] not in b"cp"]
            block = blocks[tag]
            starts = [j+1 for j,c in enumerate(cnf) if c == block[0] and cnf[j:j+len(block)]==block]
            assert len(starts)==1,(subfolder,item["case"],starts)
            print(f"{subfolder}/{item['case']}: exact positions {starts[0]}..{starts[0]+len(block)-1} ({len(block)} signed clauses)")
