#!/usr/bin/env python3
"""Compare exact order and every signed literal up to the free-lex suffix."""
import ast, hashlib, json, subprocess, sys, tempfile
from pathlib import Path

emitted, archive = map(Path,sys.argv[1:])
orig={tuple(map(int,m["pinned_words"])):m for m in json.loads((archive/"manifest.json").read_text())}
with tempfile.TemporaryDirectory() as tmp, emitted.open("rb") as f:
    def audit(meta, rows):
        target=Path(tmp)/"original.cnf"
        subprocess.run([sys.executable,str(archive/"generate.py"),meta["case"],str(target)],
                       stdout=subprocess.DEVNULL,check=True)
        src=target.read_bytes()
        assert hashlib.sha256(src).hexdigest()==meta["cnf_sha256"]
        cs=[row.strip() for row in src.splitlines() if row.strip() and row[:1] not in b"cp"]
        assert len(cs)>len(rows), (meta["case"],len(cs),len(rows))
        for i, row in enumerate(rows):
            assert cs[i]==row, (meta["case"],i+1,cs[i],row,len(cs),len(rows))
        # Every remaining row is one of the generator's opt-in lex clauses.
        assert all(r.startswith(b'-') and int(r.split(b' ',1)[0]) < -9718 for r in cs[len(rows):]), meta["case"]
        prefix_hash=hashlib.sha256(b"\n".join(rows)+b"\n").hexdigest()
        print(f"{meta['case']}: exact non-lex prefix {len(rows)}, archived lex suffix {len(cs)-len(rows)}; "
              f"original SHA-256 {meta['cnf_sha256']}; prefix SHA-256 {prefix_hash}")
    meta=None
    rows=[]
    for row in f:
        if row.startswith(b"case "):
            if meta is not None:
                audit(meta,rows)
            meta=orig.pop(tuple(ast.literal_eval(row.removeprefix(b"case ").decode())))
            rows=[]
        else:
            assert meta is not None
            rows.append(row.strip())
    audit(meta,rows)
assert not orig
