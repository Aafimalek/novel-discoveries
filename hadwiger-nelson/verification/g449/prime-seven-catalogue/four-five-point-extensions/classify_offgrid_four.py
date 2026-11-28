#!/usr/bin/env python3
"""Classify off-grid points with two G449 neighbors and a high grid neighbor."""
from argparse import ArgumentParser
from itertools import combinations
from math import comb
from pathlib import Path
import numpy as np

from two_point_replay import grid_neighbours, load_data, residue_maps

PRIMES = (43, 127, 211, 337)

def encoded(v):
    return sum(a << (8*i) for i,a in enumerate(v))


def main():
    ap = ArgumentParser(description=__doc__)
    ap.add_argument("input",type=Path)
    ap.add_argument("catalogue",type=Path)
    a = ap.parse_args()
    pts, _, edges, dirs = load_data(a.input,a.catalogue)
    centers, old = grid_neighbours(pts,dirs)
    high = sorted(tuple(a-128 for a in k)
                  for k,v in centers.items() if k not in old and isinstance(v,list) and len(v)>=3)
    assert len(high)==2429
    # Encode using powers of 256. Lookup of grid differences is exact because
    # given the observed coefficient bounds, equality of two encoded values
    # with digits in [-B,B] for B<128 forces digitwise equality mod 256.
    assert max(abs(x) for v in high for x in v) + 2*max(abs(x) for v in dirs for x in v) + max(abs(x) for v in pts for x in v) < 128
    H = [encoded(x) for x in high]
    E = {encoded(x) for x in dirs}
    n,m = len(pts),len(high)
    base_pair_centers = {}
    for k,ns in centers.items():
        if not isinstance(ns,list):
            continue
        assert all(i < j for i,j in zip(ns,ns[1:]))
        x = encoded(tuple(a-128 for a in k))
        for i,j in combinations(ns,2):
            key = i*n+j
            vals = base_pair_centers.setdefault(key,[])
            vals.append(x)
            assert len(vals)<=2

    all_mod = []
    for p in PRIMES:
        # X,Y in [0,p); U,V,W,D are nonnegative remainders.
        # Before reduction, W and D may be negative. Check both extremes.
        b = p - 1
        assert max(4*b*b, 2*b*b, b**3+49*b*b) < (1<<31)
        X,Y=residue_maps(pts + high,p)
        X,Y=X.astype(np.int32),Y.astype(np.int32)
        all_mod.append((p,X,Y))
    checks = [0]*(1+len(PRIMES))
    witnessed = 0
    for i in range(n-1):
        tail = [j for j in range(i+1,n) if (i,j) not in edges]
        for start in range(0,len(tail),32):
            js=np.asarray(tail[start:start+32],dtype=np.int32)
            p,X,Y = all_mod[0]
            u,ub=(X[js]-X[i])[:,None],(Y[js]-Y[i])[:,None]
            v,vb=(X[n:]-X[i])[None,:],(Y[n:]-Y[i])[None,:]
            U,V,W,D=u*ub%p,v*vb%p,(u-v)*(ub-vb)%p,(u*vb-ub*v)%p
            q,k=np.nonzero((U*V*W+49*D*D)%p==0)
            j=js[q]
            checks[0]+=len(js)*m
            checks[1]+=len(j)
            for l,(p,X,Y) in enumerate(all_mod[1:],2):
                u,ub,v,vb=X[j]-X[i],Y[j]-Y[i],X[n+k]-X[i],Y[n+k]-Y[i]
                U,V,W,D=u*ub%p,v*vb%p,(u-v)*(ub-vb)%p,(u*vb-ub*v)%p
                keep=(U*V*W+49*D*D)%p==0
                j,k=j[keep],k[keep]
                checks[l]+=len(j)
            for b,c in zip(j.tolist(),k.tolist()):
                assert any(H[c]-x in E for x in base_pair_centers.get(i*n+b,())), (i,b,c)
                witnessed+=1
    assert checks[0] == (comb(n,2)-len(edges))*m == 238_960_162
    assert checks[-1]==witnessed==567_847
    print(f"{checks[0]:,} triples (unordered nonadjacent base pair and high grid point).",flush=True)
    print("Surviving after each modular filter:",dict(zip(PRIMES,checks[1:])),flush=True)
    print(f"Every one of {witnessed:,} survivors has an exact grid center.",flush=True)


if __name__=="__main__":
    main()
