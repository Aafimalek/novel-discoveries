#!/usr/bin/env python3
"""Classify the sole nonprism shape with three off-grid points among six."""
from argparse import ArgumentParser
from itertools import combinations
from math import comb
from pathlib import Path
import numpy as np

from audit_layers import POWERS,mul,norm_numerator,sub
from two_point_replay import grid_neighbours,load_data,residue_maps

R2=(196,)+(0,)*11
PRIMES=(43,127,211,337)


def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path)
    p.add_argument('catalogue',type=Path)
    a=p.parse_args()
    pts,_,_,dirs=load_data(a.input,a.catalogue)
    centers,old=grid_neighbours(pts,dirs)
    hi=sorted(tuple(x-128 for x in q) for q,ns in centers.items()
              if q not in old and isinstance(ns,list) and len(ns)>=3)
    del centers,old
    n=len(hi)
    assert n==2429
    idx={q:i for i,q in enumerate(hi)}
    vals=[(p,*residue_maps(hi,p)) for p in PRIMES]
    count=[0]*len(vals)
    true_edges=0
    tri=set()
    for i in range(n-1):
        J=np.arange(i+1,n)
        for k,(p,x,y) in enumerate(vals):
            keep=(x[J]-x[i])*(y[J]-y[i])%p==196%p
            J=J[keep]
            count[k]+=len(J)
        for j in J.tolist():
            u=sub(hi[j],hi[i])
            if norm_numerator(u)!=R2:
                continue
            true_edges+=1
            for z in (7,35):
                C=add(hi[i],mul(u,POWERS[z]))
                k=idx.get(C)
                if k is not None and j<k:
                    assert norm_numerator(sub(C,hi[i]))==R2
                    assert norm_numerator(sub(C,hi[j]))==R2
                    tri.add((i,j,k))
    midpoints={}
    def midpoint_has_base(X):
        if X not in midpoints:
            # X is twice the scaled midpoint's coefficients.
            midpoints[X]=any(norm_numerator(sub(X,tuple(2*x for x in q)))==R2 for q in pts)
        return midpoints[X]
    off=potential=0
    for t in sorted(tri):
        mids=[add(hi[i],hi[j]) for i,j in combinations(t,2)]
        if any(all(x%2==0 for x in M) for M in mids):
            continue
        off+=1
        if all(midpoint_has_base(M) for M in mids):
            potential+=1
    assert comb(n,2)==2_948_806 and (true_edges,len(tri),off,potential)==(637,21,14,0)
    print(f"{comb(n,2):,} high-grid pairs; modular survivors {dict(zip(PRIMES,count))}.")
    print(f"{true_edges:,} exact distance-2 edges and {len(tri):,} exact equilateral side-2 triangles.")
    print(f"{off:,} triangles have three off-grid side midpoints; {potential:,} of these have a base neighbor at every midpoint.")


if __name__=='__main__':
    main()
