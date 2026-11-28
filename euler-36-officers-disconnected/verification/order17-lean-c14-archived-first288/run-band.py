#!/usr/bin/env python3
"""Exact project-visible closure, incremental strict Lean, balanced contiguous theorem."""
import argparse,fcntl,hashlib,json,os,subprocess,time
from pathlib import Path
import re
H=Path(__file__).resolve().parent
W=H.parent
G=H/'generated';L=H/'logs'
F=W/'euler-c14-index-production';A=W/'euler-c14-original-prefix-draft'
LEAN=W/'.lean-check/lean-4.36.0-linux/bin/lean'
ML=W/'.lean-check/mathlib4'
D=W/'euler-c14-indexed-check'
p=argparse.ArgumentParser()
p.add_argument('--execute',action='store_true')
p.add_argument('--seconds',type=int,default=285)
a=p.parse_args()
assert 40<=a.seconds<=285
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
def verify(root,file):
 lines=file.read_text().splitlines()
 assert lines
 for l in lines:
  h,name=l.split(maxsplit=1)
  assert re.fullmatch('[0-9a-f]{64}',h) and not Path(name).is_absolute()
  f=(root/name).resolve()
  assert f.is_relative_to(root.resolve()) and digest(f)==h,f
 return len(lines)
start=time.monotonic()
pins=H/'closure-pins.json'
for f,d in json.loads(pins.read_text()).items(): assert digest(W/f)==d,f
for root in (F,A):
 for m in ('CHECKED-SOURCE.sha256','CHECKED-OBJECTS.sha256'):
  print(root.name,m,verify(root,root/m),flush=True)
print('Generated source files:',verify(G,G/'BAND.sha256'),flush=True)
band=json.loads((G/'band.json').read_text())
cs=band['chunks']
assert band['baseline_end']==8897 and band['band_end']==9326 and len(cs)==23
assert cs[0]['lo']==8897 and cs[-1]['hi']==9326
assert all(x['hi']==y['lo'] for x,y in zip(cs,cs[1:]))
assert ((G/'C14ProofChunk9254_9278Draft.lean').read_bytes()==(A/'C14ProofChunk9254_9278Draft.lean').read_bytes())
if not a.execute:
 print('Static verification only. No Lean invoked.')
 raise SystemExit
lock=open('/tmp/nine-149-next/.adaptive-sequential-124-127.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
L.mkdir(exist_ok=True);(H/'tmp').mkdir(exist_ok=True)
env=os.environ.copy()
env['LEAN_PATH']=':'.join(map(str,[G,A,F,F/'generated',D,ML/'.lake/build/lib/lean',
                                   *sorted(ML.glob('.lake/packages/*/.lake/build/lib/lean'))]))
env['TMPDIR']=str(H/'tmp')
closure=digest(pins)+':'+digest(G/'BAND.sha256')
def event(s):
 print(s,flush=True)
 with (L/'events.tsv').open('a') as f:f.write(s+'\n')
def paths(m):return G/(m+'.lean'),G/(m+'.olean'),L/(m+'.log'),L/(m+'.json')
def expected(theorem, axioms):
 return f"'Euler.C14.Production.{theorem}' depends on axioms: [{axioms}]"
def good(m, audits):
 s,o,l,r=paths(m)
 if not (r.exists() and o.exists() and l.exists()): return False
 data=json.loads(r.read_text())
 now=dict(closure=closure,source=digest(s),object=digest(o),log=digest(l))
 return data==now and all(x in l.read_text().splitlines() for x in audits)
def write_atomic(f,data):
 temp=f.with_suffix(f.suffix+'.tmp');temp.write_text(json.dumps(data,indent=2)+'\n');temp.replace(f)
def run(m,audits,budget):
 if good(m,audits):event(f'{m}\treuse');return True
 s,o,l,r=paths(m)
 for f in (r,o): f.unlink(missing_ok=True)
 t=time.monotonic()
 try:
  with l.open('wb') as log:
   rcode=subprocess.run([str(LEAN),'-j1','-M2450','-DwarningAsError=true','-R',str(G),'-o',str(o),str(s)],
      env=env,stdout=log,stderr=subprocess.STDOUT,timeout=budget,check=False).returncode
 except subprocess.TimeoutExpired:rcode=124
 if (rcode!=0 or not o.is_file() or not all(x in l.read_text().splitlines() for x in audits)):
  event(f'{m}\tfail\t{rcode}\t{time.monotonic()-t:.2f}')
  return False
 write_atomic(r,dict(closure=closure,source=digest(s),object=digest(o),log=digest(l)))
 event(f'{m}\tchecked\t0\t{time.monotonic()-t:.2f}')
 return True
def audits(c):return [expected(c['theorem'],'propext')]
end=start+a.seconds
finished=[]
for c in cs:
 if good(c['module'],audits(c)):finished.append(c);continue
 remain=end-time.monotonic()
 if remain<36:break
 if not run(c['module'],audits(c),min(47,remain-25)):break
 finished.append(c)
assert all(c is cs[i] for i,c in enumerate(finished))
if not finished:
 event('no new leaf and no aggregate');raise SystemExit(2)
c=finished[-1];m=c['aggregate'];n=c['hi']
checks=[expected(f'bandThrough{n}','propext'),expected(c['final_theorem'],'propext, Classical.choice, Quot.sound')]
remaining=end-time.monotonic()
if remaining<5 or not run(m,checks,min(remaining,32)): raise SystemExit(3)
write_atomic(L/'latest-composed.json',dict(end=n,learned=n-8825,leaf_count=len(finished),theorem=c['final_theorem'],
 archive_aggregate=m,receipt=digest(paths(m)[3]),closure=closure))
print(f'Checked exact contiguous archive through slot {n} ({n-8825} learned additions).')
