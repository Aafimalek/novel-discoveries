"""Regenerate a checked all-low-pairs-used DIMACS formula."""
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
source = here / "sources" / "min2_f17_pinned.py"
args.output.parent.mkdir(parents=True, exist_ok=True)
subprocess.run([sys.executable, str(source), "allused", str(args.output),
                *meta["pinned_words"]], check=True)
computed = hashlib.sha256(args.output.read_bytes()).hexdigest()
if computed != meta["cnf_sha256"]:
    raise SystemExit(f"CNF hash mismatch: {computed} != {meta['cnf_sha256']}")
print(f"{args.case}: CNF SHA-256 {computed}")
