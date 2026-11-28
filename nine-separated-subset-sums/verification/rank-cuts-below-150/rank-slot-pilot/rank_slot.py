#!/usr/bin/env python3
"""Check oriented base forms for prescribed ranks, with exact Farkas replay."""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
from central_branch import arrays, exact, oracle
from central_matching import parse

BASE_SIGNS=('++++-+---','-------++')
RANKS=(50,64)
def signs(a):
    return ''.join('+' if x==1 else '-' for x in a)
def extra(sigma,q):
    assert len(sigma)==8 and q in (50,51,53,54,60,61,63,64)
    # alpha = sigma·x_base, 149-2q <= alpha <= x9-(2q-1).
    return [([-a for a in sigma]+[0],2*q-149),
            (list(sigma)+[-1],1-2*q)]
def calculate():
    data={}
    for z in BASE_SIGNS:
        for q in RANKS:
            good={}
            open_count=0
            unresolved=0
            for sigma in product((-1,1),repeat=8):
                x,c=oracle(parse(z),[],extra(sigma,q))
                if c is not None: good[signs(sigma)]=c
                elif x is not None: open_count+=1
                else: unresolved+=1
            data[f'{z}:{q}']={'certs':good,'numeric_feasible':open_count,'unknown':unresolved}
    return data
def replay(data):
    assert set(data)=={f'{z}:{q}' for z in BASE_SIGNS for q in RANKS}
    for key,v in sorted(data.items()):
        z,t=key.split(':'); q=int(t)
        A,b=arrays(parse(z),[])
        strict=0
        for w,y in v['certs'].items():
            assert len(w)==8 and set(w)<=set('+-')
            fresh=extra(parse(w),q)
            rhs=b+[bb for a,bb in fresh]
            assert exact(A+[a for a,bb in fresh],rhs,y),(z,q,w)
            strict+=int(sum(v*Fraction(y.get(str(i),0)) for i,v in enumerate(rhs))==0)
        print(key,'exact rejections',len(v['certs']),'oriented forms not excluded',256-len(v['certs']),
              'strict-bound leaves',strict, 'unknown from floating oracle',v['unknown'])
def main():
    p=ArgumentParser()
    p.add_argument('--verify-only',action='store_true')
    a=p.parse_args()
    f=Path('rank-slot-farkas.json')
    if a.verify_only: data=json.loads(f.read_text())
    else:
        data=calculate()
        f.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    replay(data)
if __name__=='__main__': main()
