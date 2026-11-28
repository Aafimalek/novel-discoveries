#!/usr/bin/env python3
"""Plan fixed-address independently checkable Lean modules. No Lean run."""
import gzip,json,sys
from pathlib import Path
cnf,cone=map(Path,sys.argv[1:3]);n=8825
original=[list(map(int,l.split()))[:-1] for l in cnf.read_text().splitlines()[1:]]
assert len(original)==n
with gzip.open(cone,'rt') as f: trace=json.load(f)['learned']
allrows=original+[r['clause'] for r in trace]
slots={i+1:i for i in range(n)}
slots.update((r['id'],n+k) for k,r in enumerate(trace))
chunks=[];lo=48
assert [r['id'] for r in trace[:48:24]]==[10716,10740]
while lo<len(trace):
 hi=lo; work=0
 while hi<len(trace) and hi-lo<24:
  q=trace[hi]; w=len(q['hints'])
  if hi>lo and (work+w>1800 or w >= 550):break
  hi+=1;work+=w
  if w>=550:break
 sl=trace[lo:hi];imports=sorted({slots[h] for r in sl for h in r['hints'] if slots[h]<n+lo})
 chunks.append(dict(lo=n+lo,hi=n+hi,first_id=sl[0]['id'],last_id=sl[-1]['id'],
                    hints=work,max_hints=max(len(r['hints']) for r in sl),
                    max_width=max(len(r['clause']) for r in sl),
                    learned_imports=[s for s in imports if s>=n]))
 lo=hi

def ar(xs):return '#['+', '.join(map(str,xs))+']'
def emit(c):
 lo,hi=c['lo'],c['hi']; name=f'chunk_{lo}_{hi}'
 raw=[]
 for i,r in enumerate(trace[lo-n:hi-n],lo):
  hs=[slots[h] for h in r['hints']];assert all(j<i for j in hs)
  raw.append(f"  ({r['id']}, {i}, {ar(r['clause'])}, #["+
             ', '.join(f'({j}, {ar(allrows[j])})' for j in hs)+'])')
 s='''import C14GlobalDriverDraft
namespace Euler.C14.Production
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000
def fields_'''+name+''' : Array (Nat × Nat × Array Int × Array (Nat × Array Int)) := #[
'''+',\n'.join(raw)+'''\n]
global_rup '''+f"{name} {lo} fields_{name}"+'''
#print axioms '''+name+'''
end Euler.C14.Production
'''
 Path(f'C14ProofChunk{lo}_{hi}Draft.lean').write_text(s)
emit(chunks[0])
emit(next(c for c in chunks if c['learned_imports']))
Path('planned-chunks.json').write_text(json.dumps(chunks,indent=2)+'\n')
print(len(chunks),'chunks',sum(c['hi']-c['lo'] for c in chunks),'rows',sum(c['hints'] for c in chunks),'hints')
print('next',chunks[0]);print('first cross learned',next(c for c in chunks if c['learned_imports']))
