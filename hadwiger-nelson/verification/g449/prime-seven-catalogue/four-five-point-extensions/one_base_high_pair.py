#!/usr/bin/env python3
"""Enumerate off-grid circumcenters meeting one base point and two high grid points."""
from argparse import ArgumentParser
from itertools import combinations
from math import comb
from pathlib import Path
import numpy as np

from classify_offgrid_four import encoded
from two_point_replay import grid_neighbours,load_data,residue_maps

PRIMES = (43, 127, 211, 337)


def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument("input",type=Path)
    ap.add_argument("catalogue",type=Path)
    args=ap.parse_args()
    pts,_,_,dirs=load_data(args.input,args.catalogue)
    gc,old=grid_neighbours(pts,dirs)
    high=sorted((tuple(a-128 for a in q),v)
                for q,v in gc.items() if isinstance(v,list) and len(v)>=4 and q not in old)
    n,m=len(pts),len(high)
    assert n==449 and m==1043
    P=[q for q,_ in high]
    H=[encoded(q) for q in P]
    dirs0={encoded(q) for q in dirs}
    assert len(dirs0)==len(dirs)==546
    B=max(abs(a) for q in pts for a in q)
    S=max(abs(a) for q in dirs for a in q)
    T=max(abs(a) for q in P for a in q)
    # Injectivity for all compared coefficient differences.
    assert max(T+B+2*S,2*T+S)<128
    assert all(isinstance(v,int) or all(x<y for x,y in zip(v,v[1:])) for v in gc.values())
    C={encoded(tuple(a-128 for a in q)):
        (1<<v if isinstance(v,int) else sum(1<<i for i in v)) for q,v in gc.items()}
    assert len(C)==len(gc)
    grid_witnesses={}
    for i,q in enumerate(H):
        for d in dirs0:
            x=q+d
            if x in C:
                grid_witnesses.setdefault(x,[]).append(i)
    table={}
    for x,ns in grid_witnesses.items():
        assert all(i<j for i,j in zip(ns,ns[1:]))
        for j,k in combinations(ns,2):
            l=j*m+k
            table[l]=table.get(l,0)|C[x]
    print(f"Grid-witness table: {len(table):,} high-grid pairs,",
          f"{sum(x.bit_count() for x in table.values()):,} base/high-pair triples.",flush=True)
    del C,grid_witnesses,gc
    L,R=np.triu_indices(m,1)
    H_ED=np.fromiter((H[j]-H[k] in dirs0 for j,k in zip(L,R)),bool,len(L))
    L,R=L[~H_ED].astype(np.int32), R[~H_ED].astype(np.int32)
    HBASE=np.zeros((n,m),dtype=bool)
    for k,(_,ns) in enumerate(high):
        HBASE[ns,k]=True
    # Any unit edge in a triangle of grid points forces both unit centers onto the grid.
    mods=[]
    for p in PRIMES:
        b=p-1
        assert max(4*b*b,2*b*b,b**3+49*b*b)<(1<<31)
        X,Y=residue_maps(pts+P,p)
        mods.append((p,X.astype(np.int32),Y.astype(np.int32)))
    checkpoints=[0]*(len(mods)+1)
    witnessed=0
    for i in range(n):
        flag=HBASE[i]
        for offset in range(0,len(L),65_536):
            q,r=L[offset:offset+65_536],R[offset:offset+65_536]
            keep=~(flag[q]|flag[r])
            q,r=q[keep],r[keep]
            checkpoints[0]+=len(q)
            for s,(p,X,Y) in enumerate(mods,1):
                u,ub,v,vb=X[n+q]-X[i],Y[n+q]-Y[i],X[n+r]-X[i],Y[n+r]-Y[i]
                U,V,W,D=u*ub%p,v*vb%p,(u-v)*(ub-vb)%p,(u*vb-ub*v)%p
                keep=(U*V*W+49*D*D)%p==0
                q,r=q[keep],r[keep]
                checkpoints[s]+=len(q)
            for j,k in zip(q.tolist(),r.tolist()):
                assert table.get(j*m+k,0)>>i&1, (i,j,k)
                witnessed+=1
    assert n*comb(m,2)==243_987_947 and checkpoints[0]==237_808_116
    assert checkpoints[-1] == witnessed == 353_150
    print(f"Full raw universe {n*comb(m,2):,}; {checkpoints[0]:,} triples after geometric edge exclusions.",
          flush=True)
    print("Surviving after each modular filter:",dict(zip(PRIMES,checkpoints[1:])),flush=True)
    print(f"Every one of {witnessed:,} survivors has an exact grid center.",flush=True)


if __name__=="__main__":
    main()
