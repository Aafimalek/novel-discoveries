"""Generate the archived CNF and replay an original or regenerated proof."""

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

here = Path(__file__).resolve().parent
manifest = {r["case"]: r for r in json.loads((here/"manifest.json").read_text())}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--case",action="append",choices=sorted(manifest))
options=parser.add_mutually_exclusive_group(required=True)
options.add_argument("--proof-dir",type=Path)
options.add_argument("--solve",metavar="KISSAT")
parser.add_argument("--checker", default="drat-trim")
args=parser.parse_args()

def hash(path):
    h=hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda:f.read(1<<20),b""):
            h.update(block)
    return h.hexdigest()

with tempfile.TemporaryDirectory(prefix="euler-f17-") as tmp:
    w=Path(tmp)
    for name in args.case or manifest:
        info=manifest[name]
        cnf=w/f"{name}.cnf"
        proof=w/f"{name}.drat"
        subprocess.run([sys.executable,str(here/"generate.py"),name,str(cnf)],check=True)
        if args.proof_dir:
            packed=args.proof_dir/f"{name}.drat.gz" if info["proof_encoding"]=="gzip" else args.proof_dir/f"{name}.drat"
            if hash(packed)!=info["proof_sha256"]:
                raise SystemExit(f"{name}: archived proof hash does not match")
            if info["proof_encoding"]=="gzip":
                with gzip.open(packed,"rb") as a, proof.open("wb") as b:
                    shutil.copyfileobj(a,b)
            else:
                shutil.copyfile(packed,proof)
        else:
            ret=subprocess.run([args.solve,str(cnf),str(proof)])
            if ret.returncode!=20:
                raise SystemExit(f"{name}: solver did not report UNSAT (exit {ret.returncode})")
        r=subprocess.run([args.checker,str(cnf),str(proof),"-q"],capture_output=True,text=True)
        if r.returncode!=0 or "s VERIFIED" not in r.stdout.splitlines():
            raise SystemExit(f"{name}: replay failed\n{r.stdout}\n{r.stderr}")
        print(f"{name}: VERIFIED",flush=True)
        proof.unlink()
