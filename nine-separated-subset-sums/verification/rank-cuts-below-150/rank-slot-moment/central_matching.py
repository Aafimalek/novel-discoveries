#!/usr/bin/env python3
"""Exact Farkas replay for opposite-central-sign matching cuts."""
import argparse
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
from central_root_lp import check, inequalities, verify

def matchings(s,left=tuple(range(9)),pairs=()):
    if not left:
        yield pairs
        return
    i,*tail=left
    tail=tuple(tail)
    yield from matchings(s,tail,pairs)
    for j in tail:
        if s[i]!=s[j]:
            yield from matchings(s,tuple(k for k in tail if k!=j),pairs+((i,j),))

def matching_rows(s, singleton=True):
    # Keep a concrete lex-first matching for each sum-of-lower-weights row.
    use={}
    for pairs in matchings(s):
        if not pairs: continue
        L=tuple(i for i,j in pairs)
        assert len(set(i for pair in pairs for i in pair))==2*len(L)
        assert all(i<j and s[i]==-s[j] for i,j in pairs)
        # Exactly one minus in the reduced configuration yields stronger
        # packing when its remaining dimension is at least three.
        remaining_minus=s.count(-1)-sum(s[i]==-1 for i in L)
        c=3 if singleton and remaining_minus==1 else 1
        if (L,c) not in use: use[L,c]=pairs
    # A row with larger ordered lower indices and no smaller g coefficient
    # dominates, using the sorted weights and g>=1.
    out=[]
    for (L,c),pairs in sorted(use.items()):
        if any(len(L)==len(K) and c<=d and (K,d)!=(L,c) and
               all(i<=j for i,j in zip(L,K)) for K,d in use):
            continue
        A=[(1 if i in L else -1)+c*s[i] for i in range(9)]
        b=-(2**(9-len(L))-2)
        out.append((A,b,pairs,c))
    return out

def newcuts(s,singleton):
    A,b=inequalities(s,True)
    rows=matching_rows(s,singleton)
    return A+[a for a,_,_,_ in rows],b+[d for _,d,_,_ in rows],rows

def parse(sign): return tuple(1 if c=="+" else -1 for c in sign)

def compute(base,singleton):
    import numpy as np
    from scipy.optimize import linprog
    certs={}; feasible=0; unknown=0; added=0
    for s in product((-1,1),repeat=9):
        key=''.join('+' if t==1 else '-' for t in s)
        if key in base: continue
        A,b,rows=newcuts(s,singleton)
        added+=len(rows)
        primal=linprog(np.zeros(9),A_ub=A,b_ub=b,bounds=[(None,None)]*9,method='highs')
        if primal.status==0:
            feasible+=1
            continue
        if primal.status!=2:
            unknown+=1
            continue
        dual=linprog(np.zeros(len(A)),A_eq=np.vstack((np.array(A).T,b)),
                     b_eq=[0]*9+[-1],bounds=[(0,None)]*len(A),method='highs')
        if dual.status!=0:
            unknown+=1
            continue
        for den in (1000,10000,100000,1000000,10000000):
            y=[Fraction(float(x)).limit_denominator(den) for x in dual.x]
            if check(A,b,y):
                certs[key]={str(i):str(z) for i,z in enumerate(y) if z}
                break
        else:
            unknown+=1
    return {'certs':certs,'numeric_feasible':feasible,'unknown':unknown,'matching_rows':added}

def replay(base,record,singleton):
    for sign,sparse in record['certs'].items():
        assert len(sign)==9 and set(sign)<=set('+-') and sign not in base
        s=parse(sign)
        A,b,rows=newcuts(s,singleton)
        assert all(int(i) in range(len(b)) and str(int(i))==i for i in sparse)
        y=[Fraction(sparse.get(str(i),0)) for i in range(len(b))]
        assert check(A,b,y),sign
        for row, rhs,pairs,c in rows:
            lower={i for i,j in pairs}
            assert all(0<=i<j<9 and s[i]+s[j]==0 for i,j in pairs)
            assert len({i for pair in pairs for i in pair})==2*len(pairs)
            assert c==1 or singleton and c==3 and s.count(-1)-sum(s[i]==-1 for i in lower)==1
            assert row==[c*s[i]+(1 if i in lower else -1) for i in range(9)]
            assert rhs==-(2**(9-len(pairs))-2)
    return len(record['certs'])

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--verify-only',action='store_true')
    a=p.parse_args()
    base_all=json.loads(Path('central-root-farkas.json').read_text())
    assert verify(base_all['True'],True)==294
    base=base_all['True']['verified_rejections']
    path=Path('matching-farkas.json')
    if a.verify_only: data=json.loads(path.read_text())
    else:
        data={str(c):compute(base,c) for c in (False,True)}
        path.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    for c in (False,True):
        r=data[str(c)]
        n=replay(base,r,c)
        print('Singleton enhancement:',c,'| new exact rejections:',n,
              '| not excluded:',512-len(base)-n,'| matching rows tested:',r['matching_rows'])
        if not a.verify_only: assert r['unknown']==0
if __name__=='__main__': main()
