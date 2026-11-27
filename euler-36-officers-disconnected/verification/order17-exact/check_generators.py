"""Regenerate all CNFs and validate the recorded DIMACS and log digests."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

base=Path(__file__).resolve().parent
num=0
with tempfile.TemporaryDirectory(prefix="euler-verify-formulas-") as ws:
    output=Path(ws)/"formula.cnf"
    for d in sorted(base.iterdir()):
        if not d.is_dir() or not (d/"manifest.json").is_file():
            continue
        for r in json.loads((d/"manifest.json").read_text()):
            name=r["case"]
            log=d/"replay"/f"{name}.log"
            assert "s VERIFIED" in log.read_text().splitlines(), log
            assert hashlib.sha256(log.read_bytes()).hexdigest()==r["replay_sha256"], log
            subprocess.run([sys.executable,str(d/"generate.py"),name,
                            str(output)],check=True)
            assert hashlib.sha256(output.read_bytes()).hexdigest()==r["cnf_sha256"], name
            num+=1
assert num==56,num
print(f"{num} CNFs regenerated and 56 archived replay log digests checked")
