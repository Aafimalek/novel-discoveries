"""Generate and hash-check the exact CNF of the archived single-overlap branch."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
here=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("case",choices=["one"])
parser.add_argument("output",type=Path)
args=parser.parse_args()
meta=json.loads((here/"manifest.json").read_text())[0]
subprocess.run([sys.executable,str(here/"sources/min2_f17.py"),
                args.case,str(args.output)],check=True)
h=hashlib.sha256(args.output.read_bytes()).hexdigest()
if h!=meta["cnf_sha256"]:
    raise SystemExit(f"CNF hash mismatch: {h} != {meta['cnf_sha256']}")
print(f"one: CNF SHA-256 {h}")
