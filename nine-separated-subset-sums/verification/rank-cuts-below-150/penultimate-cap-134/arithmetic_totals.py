"""Sum the actual exact per-shard rejection logs."""
from ast import literal_eval
from collections import defaultdict
import json
from pathlib import Path
import re

def stats():
    by=defaultdict(lambda:[0]*6)
    seen=set()
    source=json.loads(Path('checkpoint/manifest.json').read_text())
    ids={z['id'] for z in source['shards']}
    progress={(z['id'],z['depth']):z for f in Path('progress').glob('*.json')
              for z in [json.loads(f.read_text())]}
    for f in Path('logs').glob('a*-*.log'):
        k='-'.join(f.name.split('-')[:2])
        assert k in ids
        for q in f.read_text().splitlines():
            m=re.match(r'^depth (\d+) counts \[[^\]]+\] (\[[^\]]+\]) remain ',q)
            if not m:continue
            d=int(m[1]); c=literal_eval(m[2])
            assert len(c)==6 and all(isinstance(x,int) and x>=0 for x in c)
            assert (k,d) not in seen
            seen.add((k,d))
            assert (k,d) in progress and c[1]-sum(c[2:])==progress[k,d]['count']
            for i,x in enumerate(c):by[d][i]+=x
    assert set(progress)==seen
    for d,c in sorted(by.items()):
        print('Depth',d,': [divisibility, cells, tail, orbit-size, interval, orbit-assignment] =',c,
              '; residual cells =',c[1]-sum(c[2:]))
    print('Shard progress checkpoints with verified count identities:',len(seen))
if __name__=='__main__':stats()
