"""Resume a single deterministic disjoint shard at depth three or later."""
import argparse
import json
from pathlib import Path
from checkpoint import ROOT, atom, check_profiles, dump, load, sha

def get_seed(checkpoint, name):
    prof,m=load(checkpoint)
    z=next((v for v in m['shards'] if v['id']==name),None)
    assert z is not None, f'Unknown shard {name}'
    a=z['a']
    rows=prof[str(a)][z['lo']:z['hi']]
    h=sha(dump(rows))
    assert h==z['input_sha256']
    return a,check_profiles(rows,2),h,sha(dump(m))

def read_progress(dir,name,a,rows,h,manifest_sha):
    depth=2
    while True:
        f=dir/f'{name}-d{depth+1}.json'
        if not f.exists():break
        data=f.read_bytes()
        j=json.loads(data)
        assert data==dump(j)
        assert (j['id'],j['a'],j['depth'],j['manifest_sha256'],j['input_sha256'])==(
            name,a,depth+1,manifest_sha,h)
        assert j['residual_sha256']==sha(dump(j['residual']))
        rows=check_profiles(j['residual'],depth+1)
        assert j['count']==len(rows)
        h=j['residual_sha256']
        depth+=1
        if not rows: break
    return depth,rows,h

def status(ckpt,output):
    _,m=load(ckpt)
    by={}
    cleared=0
    for s in m['shards']:
        name=s['id']
        a,rows,h,manifest_sha=get_seed(ckpt,name)
        d,v,_=read_progress(output,name,a,rows,h,manifest_sha)
        by[d]=by.get(d,0)+1
        if not v:cleared+=1
        print(name,'a',a,'depth',d,'residual',len(v))
    print('Authenticated progress by depth:',sorted(by.items()))
    print('Cleared shards:',cleared,'of',len(m['shards']))
    print('Candidate cap 132 exclusion complete:',cleared==len(m['shards']))
    print('Progress hashes check continuity, not proof replay of prior computations.')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('shard',help='One manifest ID or status')
    p.add_argument('--checkpoint',type=Path,default=ROOT/'checkpoint')
    p.add_argument('--results',type=Path,default=ROOT/'progress')
    p.add_argument('--max-depth',type=int,choices=[3,4,5,6],default=3)
    z=p.parse_args()
    if z.shard=='status':
        status(z.checkpoint,z.results)
        return
    from anchored132 import refine
    key=z.shard
    a,rows,h,manifest_sha=get_seed(z.checkpoint,key)
    depth,rows,h=read_progress(z.results,key,a,rows,h,manifest_sha)
    print('RESUME',key,'a',a,'from depth',depth,'count',len(rows),flush=True)
    for k in range(depth+1,z.max_depth+1):
        if not rows:break
        next_rows=refine(132,{a:rows},k).get(a,[])
        check_profiles(next_rows,k)
        h2=sha(dump(next_rows))
        record={'id':key,'a':a,'depth':k,'manifest_sha256':manifest_sha,'input_sha256':h,
                'count':len(next_rows),'residual_sha256':h2,'residual':next_rows}
        f=z.results/f'{key}-d{k}.json'
        assert not f.exists()
        atom(f,dump(record))
        print('CHECKPOINT',key,'depth',k,'count',len(next_rows),'SHA256',h2,flush=True)
        rows,h=next_rows,h2
    print('CLEARED' if not rows else 'STILL OPEN',key,len(rows),flush=True)

if __name__=='__main__':main()
