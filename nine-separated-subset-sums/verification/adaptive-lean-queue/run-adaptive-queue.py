"""Build a generated Lean proof DAG with explicit dependency, hash, and exit checks."""
import argparse, concurrent.futures, fcntl, hashlib, json, os, subprocess, sys
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('manifest',type=Path)
p.add_argument('--repo',type=Path,default=Path('.'))
p.add_argument('--lean',default=os.environ.get('LEAN','lean'))
p.add_argument('--jobs',type=int,default=1)
p.add_argument('--seconds',type=int,default=180)
p.add_argument('--memory',type=int,default=3100,help='Lean memory limit per worker, MB')
p.add_argument('--log',type=Path)
args=p.parse_args()
assert min(args.jobs,args.seconds,args.memory)>0
man=json.loads(args.manifest.read_text()); mods=man['modules']
repo=args.repo.resolve(); root=repo/'NineSeparatedSubsetSums'
logs=(args.log or args.manifest.with_suffix('.logs')).resolve(); logs.mkdir(parents=True,exist_ok=True)
shelf_lock=(repo/f".adaptive-shelf-{man['second']}.lock").open('w')
fcntl.flock(shelf_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
lock=(logs/'run.lock').open('w')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)

fingerprints={}
def snd(n,anc=()):
    if n in fingerprints:return fingerprints[n]
    assert n not in anc,f'cycle at {n}'
    h=hashlib.sha256((root/f'{n}.lean').read_bytes())
    for d in mods[n]:
        h.update(snd(d,anc+(n,)).encode())
    fingerprints[n]=h.hexdigest()
    return fingerprints[n]
for n in mods:snd(n)
env=dict(os.environ)
env['LEAN_PATH']=str(repo)+((':'+env['LEAN_PATH']) if env.get('LEAN_PATH') else '')

def skip(n):
    record=logs/f'{n}.ok.json'
    if not record.is_file() or not (root/f'{n}.olean').is_file():return False
    log=logs/f'{n}.log'
    if not log.is_file():return False
    m=json.loads(record.read_text())
    return (m['source_and_deps']==fingerprints[n] and
            m['log_sha256']==hashlib.sha256(log.read_bytes()).hexdigest())

def compile(n):
    import time
    src=root/f'{n}.lean'; obj=root/f'{n}.olean'
    log=logs/f'{n}.log'; stamp=logs/f'{n}.ok.json'
    stamp.unlink(missing_ok=True)
    start=time.monotonic()
    with log.open('wb') as out:
        child=subprocess.run(['timeout','--kill-after=5',str(args.seconds),args.lean,
          '-j','1','-M',str(args.memory),'-R',str(repo),'-o',str(obj),str(src)],
          cwd=repo,env=env,stdout=out,stderr=subprocess.STDOUT)
    t=round(time.monotonic()-start,3)
    data=log.read_bytes()
    status=(child.returncode==0 and obj.is_file() and b'sorryAx' not in data
                  and b'declaration uses `sorry`' not in data)
    if status:
        stamp.write_text(json.dumps(dict(source_and_deps=fingerprints[n],
            log_sha256=hashlib.sha256(data).hexdigest(),seconds=t))+'\n')
    return n,status,child.returncode,t

todo=set(mods)
done=set()
failed=set()
active={}
with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
    while todo or active:
        ready=sorted((n for n in todo if set(mods[n])<=done),key=list(mods).index)
        for n in ready[:args.jobs-len(active)]:
            todo.remove(n)
            if skip(n):
                done.add(n)
                print('CACHED',n,flush=True)
            else:
                active[pool.submit(compile,n)]=n
        if active:
            finished,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
            for f in finished:
                active.pop(f)
                n,ok,code,t=f.result()
                (done if ok else failed).add(n)
                print('OK' if ok else 'FAILED',n,code,t,flush=True)
        elif not ready:
            break
if failed or todo:
    print('UNVERIFIED:',sorted(failed),'; blocked modules:',len(todo))
    sys.exit(1)
assert done==set(mods)
if man['final']:
    print(f"VERIFIED SHELF {man['second']}: {man['final']}")
else:
    print(f"VERIFIED REPRESENTATIVES ONLY for shelf {man['second']}: {man['targets']}")
