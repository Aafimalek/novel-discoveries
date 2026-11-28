#!/usr/bin/env python3
"""Generate exact actual archive slices and every possible prefix aggregate."""
import argparse,gzip,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('core',type=Path);p.add_argument('trace',type=Path);p.add_argument('plan',type=Path)
p.add_argument('out',type=Path)
a=p.parse_args();a.out.mkdir(exist_ok=True,parents=True)
def sha(x): return hashlib.sha256(x).hexdigest()
input_core=a.core.read_bytes();input_trace=a.trace.read_bytes()
assert sha(input_core)=='1250abf3c7bab4709e3c5d22c4c57b0beb833052bf308092690668e7346ceb50'
assert sha(input_trace)=='bc70268e380895a051d8a6c2b354a3af0dd39318d2e4595b321563d85257b101'
header,*core=input_core.splitlines();assert header.split()==[b'p',b'cnf',b'10646',b'8825']
db=[]
for l in core:
 x=list(map(int,l.split())); assert x[-1]==0
 db.append(x[:-1])
n=len(db);assert n==8825
id2slot={j+1:j for j in range(n)}; alive=set(id2slot); adds=[]
for raw in input_trace.splitlines():
 parts=raw.split()
 if parts[1]==b'd':
  d=list(map(int,parts[2:]));assert d[-1]==0 and set(d[:-1])<=alive
  alive.difference_update(d[:-1]);continue
 v=list(map(int,parts));sep=v.index(0); ident=v[0]
 h=v[sep+1:-1];assert v[-1]==0 and ident not in id2slot and all(x in alive for x in h)
 lits=v[1:sep];slot=len(db)
 adds.append((ident,slot,lits,[id2slot[x] for x in h]))
 id2slot[ident]=slot;alive.add(ident);db.append(lits)
assert len(adds)==5085 and adds[-1][0]==17658 and adds[-1][2]==[]
all_chunks=json.loads(a.plan.read_text())
assert all_chunks[0]['lo']==8873 and all_chunks[0]['hi']==8897
assert all(x['hi']==y['lo'] for x,y in zip(all_chunks,all_chunks[1:])) and all_chunks[-1]['hi']==13910
chunks=[c for c in all_chunks if c['lo']>=8897 and c['hi']<=9326]
assert len(chunks)==23 and chunks[0]['lo']==8897 and chunks[-1]['hi']==9326
def ar(xs):return '#['+', '.join(map(str,xs))+']'
def tname(c):return f"chunk_{c['lo']}_{c['hi']}"
def cname(c):return f"C14ProofChunk{c['lo']}_{c['hi']}Draft"
def write(name,text): (a.out/ (name+'.lean')).write_text(text)
for c in chunks:
 lo,hi=c['lo'],c['hi'];sub=adds[lo-n:hi-n]
 assert sub[0][0]==c['first_id'] and sub[-1][0]==c['last_id']
 assert sum(len(hs) for _,_,_,hs in sub)==c['hints']
 learned=sorted({k for _,_,_,hs in sub for k in hs if n<=k<lo})
 assert learned==c['learned_imports']
 raw=[]
 for ident,slot,lits,hints in sub:
  raw.append(f'  ({ident}, {slot}, {ar(lits)}, #['+
      ', '.join(f'({j}, {ar(db[j])})' for j in hints)+'])')
 name=tname(c); mod=cname(c)
 write(mod,'import C14GlobalDriverDraft\nnamespace Euler.C14.Production\n'+
   'set_option maxRecDepth 18000\nset_option maxHeartbeats 2400000\n'+
   f'def fields_{name} : Array (Nat × Nat × Array Int × Array (Nat × Array Int)) := #[\n'+
   ',\n'.join(raw)+f'\n]\nglobal_rup {name} {lo} fields_{name}\n#print axioms {name}\nend Euler.C14.Production\n')
 c.update(module=mod,theorem=name)
def compose(cs):
 if len(cs)==1:return '('+tname(cs[0])+' base)'
 mid=len(cs)//2
 return f'(compose {compose(cs[:mid])} {compose(cs[mid:])})'
for k,c in enumerate(chunks,1):
 use=chunks[:k];end=c['hi']; name=f'C14ExactThrough{end}'
 write(name,'import C14OriginalFirst72Draft\n'+''.join(f"import {x['module']}\n" for x in use)+
  f'''\nnamespace Euler.C14.Production
open Euler.C14.IndexedDraft
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

theorem bandThrough{end} (base : Sat.Fmla) : Slice base rowAt 8897 {end} :=
  {compose(use)}

theorem exactArchiveThrough{end} : GoodBelow archivedGlobalCore rowAt {end} :=
  bandThrough{end} archivedGlobalCore first72_fromExactGlobalArchive

#print axioms bandThrough{end}
#print axioms exactArchiveThrough{end}
end Euler.C14.Production
''')
 c.update(aggregate=name,final_theorem=f'exactArchiveThrough{end}')
out=dict(source_core=sha(input_core),source_lrat=sha(input_trace),baseline_end=8897,band_end=9326,
         chunks=chunks)
(a.out/'band.json').write_text(json.dumps(out,indent=2)+'\n')
sources=sorted([*a.out.glob('*.lean'),a.out/'band.json'])
(a.out/'BAND.sha256').write_text(''.join(f'{sha(x.read_bytes())}  {x.name}\n' for x in sources))
print(f'{len(chunks)} slices, {9326-8897} later additions, {sum(c["hints"] for c in chunks)} hints')
