"""Repeat the unanchored 17-point comparison at the same 180-second budget."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess
import sys
import time

if len(sys.argv) != 3:
    raise SystemExit("usage: python3 compare_controls.py /path/to/kissat path/to/endpoint-benchmark")
solver, src = sys.argv[1:]
src = Path(src)
def run(form):
    start = time.monotonic()
    log = Path(f"{form}-17-6.same-limit.log")
    with log.open("w") as out:
        try:
            rc = subprocess.run([solver, str(src/f"{form}-17-6.cnf")], stdout=out,
                                stderr=out, timeout=180).returncode
        except subprocess.TimeoutExpired:
            rc = 124
    status = next((s for s in log.read_text().splitlines() if s.startswith("s ")), "")
    return form, round(time.monotonic()-start, 3), 180, rc, status
with ThreadPoolExecutor(max_workers=2) as ex:
    for row in ex.map(run, ["dp", "compact"]):
        print(*row, sep="\t")
