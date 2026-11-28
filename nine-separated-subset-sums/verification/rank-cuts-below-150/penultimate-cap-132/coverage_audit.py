"""Independently validate manifest coverage and SHA continuity of all stored depths."""
import hashlib
import json
from pathlib import Path

def digest(x):return hashlib.sha256(x).hexdigest()
def enc(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def read(path):
    raw=Path(path).read_bytes(); obj=json.loads(raw)
    assert raw==enc(obj),path
    return obj,digest(raw)

if __name__=='__main__':
    profiles,seed=read('checkpoint/profiles.json')
    manifest,m=read('checkpoint/manifest.json')
    assert seed=='e7e08f6b2e5e42fd95a8ba59c59f49e3746f870a8d21cd3c4f3c558b5e3cbc99'
    assert m=='fcf701bbc6934f42bf802b49b95b39ab009cd705c6a19ab6758192ea713bbef6'
    assert manifest['profiles_sha256']==seed
    assert manifest['cap']==132 and manifest['x8_lower']==132
    for f,h in manifest['source_sha256'].items():
        assert digest(Path(f).read_bytes())==h
    covers={a:[] for a in profiles}
    complete=[]; known=set(); ids=set()
    for s in manifest['shards']:
        k=s['id'];a=str(s['a'])
        assert k not in ids
        ids.add(k)
        lo,hi=s['lo'],s['hi']
        assert 0<=lo<hi<=len(profiles[a]) and hi-lo<=128
        covers[a].extend(range(lo,hi))
        h=digest(enc(profiles[a][lo:hi]))
        assert h==s['input_sha256']
        # Every shard here cleared in depth three or four, and nowhere else.
        for depth in (3,4):
            f=f'progress/{k}-d{depth}.json';known.add(f)
            z,_=read(f)
            assert z['manifest_sha256']==m and z['input_sha256']==h
            assert z['id']==k and z['a']==s['a'] and z['depth']==depth
            h=digest(enc(z['residual']))
            assert h==z['residual_sha256'] and z['count']==len(z['residual'])
            if not z['residual']:
                complete.append((k,depth))
                break
        else: raise AssertionError(f'Uncleared shard {k}')
    for a,i in covers.items(): assert sorted(i)==list(range(len(profiles[a])))
    assert sum(map(len,profiles.values()))==8426
    assert known=={str(p) for p in Path('progress').glob('*.json')}
    assert len(complete)==70 and sum(d==3 for _,d in complete)==67
    print('Independent coverage: 8,426 profiles, exactly 70 shards, no holes/overlap.')
    print('Depth-4 shards:',[k for k,d in complete if d==4])
    print('Every canonical progress chain clears; use guarded replay for proof computation.')
