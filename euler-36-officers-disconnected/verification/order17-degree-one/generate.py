"""Regenerate a DIMACS instance from the recorded exact formula construction."""

import argparse
import hashlib
import json
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
manifest = {r["case"]: r for r in json.loads((here/"manifest.json").read_text())}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("case", choices=sorted(manifest))
parser.add_argument("output", type=Path)
args = parser.parse_args()
meta = manifest[args.case]
source = here / "sources" / meta["source"]
code = source.read_text()
sys.path.insert(0,str(source.parent))
sys.argv = [str(source), "17", "1", "cnf-only", *meta["arguments"]]
scope = {"__name__":"__main__", "__file__":str(source)}
exec(compile(code,str(source),"exec"),scope)
scope["F"].to_file(str(args.output))
computed = hashlib.sha256(args.output.read_bytes()).hexdigest()
if computed != meta["cnf_sha256"]:
    raise SystemExit(f"CNF hash mismatch: {computed} != {meta['cnf_sha256']}")
print(f"{meta['case']}: CNF SHA-256 {computed}")
