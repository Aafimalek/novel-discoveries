#!/usr/bin/env python3
"""Exact high-grid circumcenter pruning for six new points around G449."""
from argparse import ArgumentParser
from itertools import combinations
from math import comb
from pathlib import Path
import numpy as np

from two_point_replay import grid_neighbours, load_data, residue_maps
from classify_offgrid_four import encoded

PRIMES=(43,127,211,337)


def main():
    pa=ArgumentParser(description=__doc__)
    pa.add_argument("input",type=Path)
    pa.add_argument("catalogue",type=Path)
    a=pa.parse_args()
    pts,_,_,dirs=load_data(a.input,a.catalogue)
    centers,old=grid_neighbours(pts,dirs)
    P=sorted(tuple(t-128 for t in q) for q,v in centers.items()
             if isinstance(v,list) and len(v)>=4 and q not in old)
    del centers,old
    n=len(P)
    assert n==1043
    H=[encoded(q) for q in P]
    D={encoded(q) for q in dirs}
    T=max(abs(a) for q in P for a in q)
    S=max(abs(a) for q in dirs for a in q)
    assert 2*(T+S)<128
    assert len(H)==len(set(H)) and len(D)==len(dirs)
    st= {}
    for i,q in enumerate(H):
        for d in D:
            x=q+d
            p=st.get(x)
            if p is None:
                st[x]=i
            elif isinstance(p,int):
                st[x]=[p,i]
            else:
                p.append(i)
    witnessed=set()
    for ns in st.values():
        if isinstance(ns,list):
            assert all(i<j for i,j in zip(ns,ns[1:]))
            witnessed.update((i*n+j)*n+k for i,j,k in combinations(ns,3))
    del st
    assert len(witnessed)==146804
    print(f"{len(witnessed):,} triples share a verified grid center.",flush=True)
    idx={v:i for i,v in enumerate(H)}
    adj=np.zeros((n,n),dtype=bool)
    for i,x in enumerate(H):
        for d in D:
            j=idx.get(x+d)
            if j is not None:
                adj[i,j]=True
    assert not adj.diagonal().any() and (adj==adj.T).all()
    L,R=np.triu_indices(n,1)
    keep=~adj[L,R]
    L,R=L[keep].astype(np.int32),R[keep].astype(np.int32)
    mods=[]
    for p in PRIMES:
        b=p-1
        assert max(4*b*b,2*b*b,b**3+49*b*b)<(1<<31)
        X,Y=residue_maps(P,p)
        mods.append((p,X.astype(np.int32),Y.astype(np.int32)))
    counts=[0]*(len(mods)+1)
    n_witnessed=0
    for i in range(n-2):
        start=np.searchsorted(L,i+1)
        flag=adj[i]
        for lo in range(start,len(L),65_536):
            j,k=L[lo:lo+65_536],R[lo:lo+65_536]
            ok=~(flag[j]|flag[k])
            j,k=j[ok],k[ok]
            counts[0]+=len(j)
            for h,(p,X,Y) in enumerate(mods,1):
                u,ub,v,vb=X[j]-X[i],Y[j]-Y[i],X[k]-X[i],Y[k]-Y[i]
                U,V,W,D0=u*ub%p,v*vb%p,(u-v)*(ub-vb)%p,(u*vb-ub*v)%p
                keep=(U*V*W+49*D0*D0)%p==0
                j,k=j[keep],k[keep]
                counts[h]+=len(j)
            for b,c in zip(j.tolist(),k.tolist()):
                assert (i*n+b)*n+c in witnessed, (i,b,c)
                n_witnessed+=1
    assert comb(n,3)==188_560_841 and counts[0]==186_404_358
    assert counts[-1]==n_witnessed==133_371
    print(f"Universe {comb(n,3):,} unordered high-grid triples, {counts[0]:,} independent.",flush=True)
    print("Survivors:",dict(zip(PRIMES,counts[1:])),flush=True)
    print(f"Every one of {n_witnessed:,} survivors has an exact grid center.",flush=True)


if __name__=="__main__":
    main()
