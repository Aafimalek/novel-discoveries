#!/usr/bin/env python3
"""Single pinned run, proof cap 128 MiB, exact validation only."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
import re
import resource
import shutil
import subprocess
import time

HERE=Path(__file__).resolve().parent
PINNED="91359c03b06fac5fbf9b5df9d30aa8d05603e76e0ad2c7705de6f673f9ad61ab"
SN=44
MEM=120*1024*1024
FCAP=128*1024*1024

def digest(p):
    h=sha256()
    with p.open("rb") as f:
        for s in iter(lambda:f.read(1024*1024),b""):h.update(s)
    return h.hexdigest()

def guard():
    for res,lim in [(resource.RLIMIT_AS,MEM),(resource.RLIMIT_FSIZE,FCAP),
                    (resource.RLIMIT_CORE,0)]:
        resource.setrlimit(res,(lim,lim))

def bounded(cmd,dir,timer,tag):
    t=time.monotonic()
    with (dir/(tag+".stdout")).open("wb") as f,(dir/(tag+".stderr")).open("wb") as e:
        try:
            rc=subprocess.run(list(map(str,cmd)),stdout=f,stderr=e,timeout=timer,
                              preexec_fn=guard,cwd=dir).returncode
        except subprocess.TimeoutExpired:
            rc="TIMEOUT"
    return rc,round(time.monotonic()-t,3)

def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument("--solver",required=True,type=Path)
    p.add_argument("--checker",required=True,type=Path)
    p.add_argument("--run-dir",required=True,type=Path)
    a=p.parse_args()
    solver,checker=a.solver.resolve(strict=True),a.checker.resolve(strict=True)
    run=a.run_dir.resolve()
    assert shutil.disk_usage(run.parent).free>=4*FCAP,"use a fresh overlay with disk space"
    run.mkdir(exist_ok=False)
    source=HERE/"raw_x0_14_strong.cnf"
    assert digest(source)==PINNED
    cnf=run/"raw_x0_14_strong.cnf"
    shutil.copyfile(source,cnf)
    assert digest(cnf)==PINNED
    (run/"invocation.sha256").write_text(
        f"{PINNED}  {cnf}\n{digest(solver)}  {solver}\n{digest(checker)}  {checker}\n")
    proof=run/"solver.drat"
    rc,wall=bounded([solver,cnf,proof],run,SN,"solver")
    s=(run/"solver.stdout").read_text(errors="replace")
    outcome="UNKNOWN"
    receipt=[f"solver config: one worker; timeout {SN}s; AS≤{MEM} bytes; files≤{FCAP} bytes",
             f"solver status {rc}; elapsed {wall}s",
             f"solver-phase peak child RSS {resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} KiB"]
    assert digest(cnf)==PINNED
    if rc==10 and re.search(r"^s SATISFIABLE\s*$",s,re.M):
        import strong
        try:
            e=strong.Strong(14)
            model=strong.read_model(run/"solver.stdout")
            dag=e.check_model(model) # 33,655 exact rows and all 256 evaluations
        except (AssertionError,ValueError,KeyError) as q:
            receipt.append("SAT model rejected: "+repr(q))
        else:
            (run/"verified-model.txt").write_text(
                "".join(f"{i+9} {op} {l} {r}\n" for i,(op,l,r) in enumerate(dag)))
            outcome="VERIFIED SAT fixed-NOT(x0)"
    elif rc==20 and re.search(r"^s UNSATISFIABLE\s*$",s,re.M) and proof.is_file() and proof.stat().st_size:
        # Replay only after clean completed solver status, never a partial trace.
        rc2,wall2=bounded([checker,cnf,proof],run,44,"checker")
        chk=(run/"checker.stdout").read_text(errors="replace")
        receipt.append(f"checker status {rc2}; elapsed {wall2}s")
        if rc2==0 and re.search(r"^s VERIFIED\s*$",chk,re.M):
            outcome="VERIFIED UNSAT fixed-NOT(x0)"
    assert digest(cnf)==PINNED
    if proof.is_file():
        if outcome!="VERIFIED UNSAT fixed-NOT(x0)":
            q=run/"unverified-proof-stream.drat"
            proof.rename(q)
            proof=q
        receipt.append(f"retained trace: {proof.name}, {proof.stat().st_size} bytes")
        (run/"trace.sha256").write_text(f"{digest(proof)}  {proof.name}\n")
    receipt.append(outcome)
    (run/"status.txt").write_text("\n".join(receipt)+"\n")
    print("\n".join(receipt))

if __name__=="__main__":main()
