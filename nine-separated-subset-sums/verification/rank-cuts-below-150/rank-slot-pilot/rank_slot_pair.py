#!/usr/bin/env python3
"""Rational replay of two required rank slots imposed on the same weights."""
import argparse
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
from central_branch import arrays, exact, oracle
from central_matching import parse
from rank_slot import BASE_SIGNS, extra, replay as replay_single

def allforms(): return map(''.join,product('-+',repeat=8))

def survivors(certs,central,q):
    return [s for s in allforms() if s not in certs[f'{central}:{q}']['certs']]

def pair_rows(q50,q64):
    a=parse(q50); c=parse(q64)
    diff=[x-y for x,y in zip(a,c)]
    # alpha50-alpha64=2*(s207-s193), with 14 gaps and excess <=(1+delta)/2.
    return extra(a,50)+extra(c,64)+[([-z for z in diff]+[0],-28),(diff+[-1],-120)]

def compute(central,data):
    cert={}; count=0; unknown=0
    s=parse(central)
    for a,c in product(survivors(data,central,50),survivors(data,central,64)):
        x,proof=oracle(s,[],pair_rows(a,c))
        if proof is not None: cert[a+'/'+c]=proof
        elif x is not None: count+=1
        else: unknown+=1
    return {'certs':cert,'numerical_feasible':count,'unknown':unknown}

def replay(central,data,record):
    A,b=arrays(parse(central),[])
    S,T=map(set,(survivors(data,central,50),survivors(data,central,64)))
    strict=0
    for k,y in record['certs'].items():
        a,c=k.split('/')
        assert a in S and c in T
        rs=pair_rows(a,c)
        rhs=b+[v for _,v in rs]
        assert exact(A+[r for r,_ in rs],rhs,y)
        strict+=int(sum(v*Fraction(y.get(str(i),0)) for i,v in enumerate(rhs))==0)
    n=len(record['certs'])
    print(central, 'single survivors',len(S),len(T),'tested',len(S)*len(T),
          'exact exclusions',n,'not excluded',len(S)*len(T)-n,
          'strict-bound leaves',strict,'unknown from float oracle',record['unknown'])

def main():
    p=argparse.ArgumentParser()
    p.add_argument('central',choices=BASE_SIGNS)
    p.add_argument('--verify-only',action='store_true')
    a=p.parse_args(); central=a.central
    data=json.loads(Path('rank-slot-farkas.json').read_text())
    replay_single(data)
    dst=Path(f'pair-{central}-farkas.json')
    if a.verify_only: record=json.loads(dst.read_text())
    else:
        record=compute(central,data)
        dst.write_text(json.dumps(record,sort_keys=True,separators=(',',':'))+'\n')
    replay(central,data,record)
if __name__=='__main__': main()
