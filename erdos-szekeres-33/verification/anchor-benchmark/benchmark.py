from pathlib import Path
import subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

K = sys.argv[1]
jobs = [
    ('anchor-5-7', 20, False),
    ('anchor-5-8', 20, True),
    ('anchor-6-15', 45, False),
    ('anchor-6-16', 180, False),
    ('anchor-7-32', 120, False),
]
def run(job):
    name, cap, proof = job
    path = Path(name + '.log')
    cmd = [K, name+'.cnf']
    if proof:
        cmd.append(name+'.drat')
    t=time.monotonic()
    with path.open('w') as f:
        try:
            proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, timeout=cap)
            rc = proc.returncode
        except subprocess.TimeoutExpired:
            rc = 124
    summary = next((x for x in path.read_text().splitlines() if x.startswith('s ')), '')
    return name, round(time.monotonic()-t, 3), cap, rc, summary

with ThreadPoolExecutor(max_workers=4) as pool:
    for row in pool.map(run, jobs):
        print(*row, sep='\t', flush=True)
