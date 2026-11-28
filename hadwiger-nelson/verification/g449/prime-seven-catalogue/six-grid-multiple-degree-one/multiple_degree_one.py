#!/usr/bin/env python3
"""Exact six-point all-grid replay for at least two additions of base degree one."""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations,product
from math import comb
from pathlib import Path
import numpy as np

from audit_layers import POWERS,mul,norm_numerator,sub
from two_point_replay import grid_neighbours,load_data,residue_maps

PRIMES=(43,127,211,337)

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,k):return tuple(x*k for x in a)

def pairs_at_norm(P,norm):
    """Exact after modular prefilters; no witness is accepted by residues alone."""
    vals=[(p,*residue_maps(P,p)) for p in PRIMES]
    N=(norm,)+(0,)*11
    for i in range(len(P)-1):
        J=np.arange(i+1,len(P))
        for p,x,y in vals:
            keep=(x[J]-x[i])*(y[J]-y[i])%p==norm%p
            J=J[keep]
        for j in J.tolist():
            if norm_numerator(sub(P[j],P[i]))==N:
                yield i,j


def minimum_total_degree(rows,dirs,deg):
    internal=[0]*6
    for i,j in combinations(range(6),2):
        if sub(rows[i],rows[j]) in dirs:
            internal[i]+=1
            internal[j]+=1
    return min(a+b for a,b in zip(deg,internal))


def main():
    pa=ArgumentParser(description=__doc__)
    pa.add_argument('input',type=Path)
    pa.add_argument('catalogue',type=Path)
    args=pa.parse_args()
    pts,_,_,dirs=load_data(args.input,args.catalogue)
    centers,old=grid_neighbours(pts,dirs)
    lows={k for k,v in centers.items() if k not in old and isinstance(v,int)}
    high={}
    for k,v in centers.items():
        if k in old or isinstance(v,int):continue
        assert all(i<j for i,j in zip(v,v[1:]))
        high[tuple(j-128 for j in k)]=len(v)
    del centers,old
    def is_low(q):
        return all(-128<=c<128 for c in q) and bytes(c+128 for c in q) in lows
    assert len(lows)==222264 and len(high)==7056
    H=sorted(high)
    high3={q for q,n in high.items() if n>=3}
    assert len(high3)==2429
    exact=possible2=0
    stats=Counter()
    for i,j in pairs_at_norm(H,147):
        exact+=1
        A,B=H[i],H[j]
        R=mul(sub(B,A),POWERS[7])
        X=add(add(scale(A,2),B),R)
        Y=sub(add(A,scale(B,2)),R)
        assert all(c%3==0 for c in X+Y)
        X=tuple(c//3 for c in X)
        Y=tuple(c//3 for c in Y)
        if not is_low(X) or not is_low(Y):continue
        possible2+=1
        assert sub(X,Y) in dirs
        assert all(sub(q,z) in dirs for q in (X,Y) for z in (A,B))
        # Each low point has exactly one additional new neighbor, unique to it.
        ns=[sorted(q for d in dirs if (q:=add(U,d)) in high and sub(q,V) not in dirs)
            for U,V in ((X,Y),(Y,X))]
        for C,D in product(*ns):
            Q=(X,Y,A,B,C,D)
            assert len(set(Q))==6
            v=minimum_total_degree(Q,dirs,(1,1,high[A],high[B],high[C],high[D]))
            assert v<5,Q
            stats[v]+=1
    assert exact==5691 and possible2==21 and sum(stats.values())==1967
    print(f"{comb(len(H),2):,} high pairs; {exact:,} exact sqrt(3) pairs; {possible2:,} hub pairs with two degree-one centers.")
    print("Exactly two degree-one case counts by minimum total degree:",dict(sorted(stats.items())),flush=True)

    tris=set()
    P=sorted(high3)
    J={q:i for i,q in enumerate(P)}
    norm2=0
    for i,j in pairs_at_norm(P,196):
        norm2+=1
        a,b=P[i],P[j]
        for k0 in (7,35):
            c=add(a,mul(sub(b,a),POWERS[k0]))
            k=J.get(c)
            if k is not None and j<k:
                assert norm_numerator(sub(c,a))==(196,)+(0,)*11
                assert norm_numerator(sub(c,b))==(196,)+(0,)*11
                tris.add((i,j,k))
    assert norm2==637 and len(tris)==21
    three_grid=three_low=0
    for t in sorted(tris):
        A,B,C=[P[i] for i in t]
        M=[add(q,r) for q,r in combinations((A,B,C),2)]
        if any(any(x%2 for x in q) for q in M):continue
        lows3=tuple(tuple(x//2 for x in q) for q in M)
        three_grid+=1
        if all(is_low(q) for q in lows3):
            three_low+=1
    print(f"{comb(len(P),2):,} high3 pairs; {norm2:,} exact distance-two pairs; {len(tris)} side-two equilateral triangles.")
    assert three_low==0
    print(f"{three_grid} triangles have three grid midpoints; {three_low} have three degree-one grid midpoints.",flush=True)


if __name__=='__main__':main()
