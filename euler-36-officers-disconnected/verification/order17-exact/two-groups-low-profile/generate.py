"""Regenerate a checked low-profile double-overlap DIMACS formula."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

here = Path(__file__).resolve().parent
manifest = {r["case"]: r for r in json.loads((here/"manifest.json").read_text())}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("case", choices=sorted(manifest))
parser.add_argument("output", type=Path)
args = parser.parse_args()
meta = manifest[args.case]
subprocess.run([sys.executable, str(here/"sources/double_low.py"), meta["diagram"],
                str(meta["low_group"]), str(args.output)], check=True)
computed = hashlib.sha256(args.output.read_bytes()).hexdigest()
if computed != meta["cnf_sha256"]:
    raise SystemExit(f"CNF hash mismatch: {computed} != {meta['cnf_sha256']}")
print(f"{args.case}: CNF SHA-256 {computed}")
