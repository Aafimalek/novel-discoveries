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
    assert seed=='12020d63c5f81f565d36e40fd73af49b9b7178f814c4ec54fb4a281e2713a43f'
    assert m=='d953ef42142b891672eed8bf1b4504d94f2544c889d6b5392ffe79e258244a74'
    assert manifest['profiles_sha256']==seed
    assert manifest['cap']==133 and manifest['x8_lower']==133
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
        for depth in (3,4,5,6):
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
    assert sum(map(len,profiles.values()))==12512
    assert known=={str(p) for p in Path('progress').glob('*.json')}
    assert len(complete)==104
    print('Independent coverage: 12,512 profiles, exactly 104 shards, no holes/overlap.')
    print('Depth-4 shards:',[k for k,d in complete if d==4])
    print('Every canonical progress chain clears; use guarded replay for proof computation.')
