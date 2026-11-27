#!/usr/bin/env python3
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from subprocess import run, TimeoutExpired
from time import perf_counter
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("kissat")
parser.add_argument("--limit", type=float, default=35.0)
args = parser.parse_args()
cases = [(m, k, f) for m, k in ((8,5),(9,5),(16,6),(17,6)) for f in ("dp","compact")]
Path("results").mkdir(exist_ok=True)

def calc(job):
    m, k, form = job
    tag = f"{form}-{m}-{k}"
    with open(f"results/{tag}.log", "wb") as out:
        start = perf_counter()
        try:
            p = run([args.kissat, tag+".cnf"], stdout=out, stderr=out,
                    timeout=args.limit, check=False)
            rc = p.returncode
            status = {10:"SAT", 20:"UNSAT"}.get(rc, "ERROR")
        except TimeoutExpired:
            rc, status = 124,"TIMEOUT"
        elapsed = perf_counter()-start
    return f"{tag}\t{status}\t{elapsed:.3f}\t{rc}"

print("instance\tresult\tseconds\texit", flush=True)
with ThreadPoolExecutor(max_workers=2) as pool:
    for results in pool.map(calc, cases):
        print(results, flush=True)
