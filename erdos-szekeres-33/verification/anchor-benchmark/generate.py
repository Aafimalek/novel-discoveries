"""Generate the normalized ES controls and target from the pinned upstream DP."""
from pathlib import Path
import hashlib
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: python3 generate.py path/to/endpoint-benchmark/upstream")
sys.path.insert(0, str(Path(sys.argv[1]).resolve()))
from lib.erdos import etv_signotope

for k, n in [(5, 7), (5, 8), (6, 15), (6, 16), (7, 32)]:
    f = Path(f"anchor-{k}-{n}.cnf")
    etv_signotope(k, k, k-1, n).write(f)
    print(f.name, next(x for x in f.open() if x.startswith('p ')).strip(),
          hashlib.sha256(f.read_bytes()).hexdigest(), sep="\t")
