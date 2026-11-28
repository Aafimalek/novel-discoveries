"""Exact phase-2 freeze and deterministic cap-133 shard manifests."""
import argparse
import hashlib
import json
import os
from pathlib import Path

ROOT=Path(__file__).resolve().parent
CAP=133
CHUNK=128
SOURCES=('anchored133.py','cap_moment.py','cap127_safe.py','orbit.py','checkpoint.py','refine_shard.py','run-shard.sh')

def dump(o):
    return (json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()

def sha(data):
    return hashlib.sha256(data).hexdigest()

def atom(path,data):
    path=Path(path)
    path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_name(path.name+f'.new-{os.getpid()}')
    tmp.write_bytes(data)
    os.replace(tmp,path)

def source_manifest():
    return {p:sha((ROOT/p).read_bytes()) for p in SOURCES}

def check_profiles(profiles,k):
    out=[]
    for l,h,lo,hi in profiles:
        assert all(type(i) is int for i in [*l,*h,lo,hi])
        assert len(l)==len(h)==k
        assert all(0<=a<=b<=a+1<=127 for a,b in zip(l,h))
        assert all(l[i]>=l[i+1] or h[i]>=l[i+1] for i in range(k-1))
        assert 0<=lo<=hi
        out.append((tuple(l),tuple(h),lo,hi))
    return out

def shard_rows(profiles):
    out=[]
    for a in sorted(map(int,profiles)):
        v=profiles[str(a)]
        check_profiles(v,2)
        assert v and len({tuple(row[0]) for row in v})==len(v)
        for j,lo in enumerate(range(0,len(v),CHUNK)):
            hi=min(lo+CHUNK,len(v))
            out.append({'id':f'a{a}-s{j:02}', 'a':a,'lo':lo,'hi':hi,
                        'input_sha256':sha(dump(v[lo:hi]))})
    return out

def manifest(profiles):
    assert all(str(a) in {str(k) for k in range(64,75)} for a in profiles)
    shards=shard_rows(profiles)
    return {'schema':1,'cap':CAP,'x8_lower':133,'depth':2,
            'profiles_sha256':sha(dump(profiles)),
            'source_sha256':source_manifest(),
            'count':sum(map(len,profiles.values())),'chunk':CHUNK,
            'shards':shards}

def load(directory):
    d=Path(directory)
    payload=(d/'profiles.json').read_bytes()
    checked=json.loads(payload)
    record=(d/'manifest.json').read_bytes()
    m=json.loads(record)
    assert payload==dump(checked)
    assert record==dump(m)
    assert m==manifest(checked), 'Manifest/digest/coverage/source mismatch'
    return checked,m

def compute():
    from anchored133 import phase2
    return {str(a):v for a,v in phase2(CAP).items()}

def main():
    p=argparse.ArgumentParser()
    p.add_argument('operation',choices=['freeze','check','replay'])
    p.add_argument('--directory',type=Path,default=ROOT/'checkpoint')
    a=p.parse_args()
    d=a.directory
    if a.operation=='freeze':
        assert not (d/'profiles.json').exists() and not (d/'manifest.json').exists(), 'refusing to overwrite frozen checkpoint'
        x=compute()
        m=manifest(x)
        atom(d/'profiles.json',dump(x))
        atom(d/'manifest.json',dump(m))
    x,m=load(d)
    if a.operation=='replay':
        # Compute fresh from the checked root; verify every enclosing profile,
        # rather than trusting the stored counts or the hash alone.
        fresh=compute()
        assert dump(fresh)==dump(x), 'Exact phase-2 replay disagrees'
    print('phase 2:',m['count'],'profiles;',len(m['shards']),'disjoint shards;',
          'payload SHA256',m['profiles_sha256'])
    print('manifest SHA256',sha(dump(m)))

if __name__=='__main__':main()
