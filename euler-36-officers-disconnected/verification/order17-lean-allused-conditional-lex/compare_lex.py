#!/usr/bin/env python3
"""Compare every generated suffix row against each exact original."""
import ast, hashlib, json, subprocess, sys, tempfile
from pathlib import Path

emitted, archive = map(Path, sys.argv[1:])
drivers={tuple(map(int,m["pinned_words"])):m for m in json.loads((archive/"manifest.json").read_text())}
suffixes={}
for row in emitted.read_bytes().splitlines():
    if row.startswith(b"case "):
        codes=tuple(ast.literal_eval(row.removeprefix(b"case ").decode()))
        assert codes not in suffixes
        suffixes[codes]=[]
    else:
        suffixes[codes].append(row)
assert set(drivers)==set(suffixes) and len(suffixes)==17
with tempfile.TemporaryDirectory() as tmp:
    path=Path(tmp)/"original.cnf"
    for codes,meta in drivers.items():
        subprocess.run([sys.executable,str(archive/"generate.py"), meta["case"], str(path)],
                       stdout=subprocess.DEVNULL,check=True)
        raw=path.read_bytes()
        assert hashlib.sha256(raw).hexdigest()==meta["cnf_sha256"]
        rows=[r.strip() for r in raw.splitlines() if r.strip() and r[:1] not in b"cp"]
        suffix=suffixes[codes]
        assert suffix and rows[-len(suffix):]==suffix,meta["case"]
        dg=hashlib.sha256(b"\n".join(suffix)+b"\n").hexdigest()
        print(f"{meta['case']}: exact lex suffix {len(suffix)}; original SHA-256 {meta['cnf_sha256']}; suffix SHA-256 {dg}")
