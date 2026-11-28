#!/usr/bin/env python3
"""Exact center-pair check for all remaining two-off six-point shapes."""
from argparse import ArgumentParser
from math import comb
from pathlib import Path
import numpy as np

from audit_layers import POWERS,mul,norm_numerator,sub
from two_point_replay import grid_neighbours,load_data,residue_maps

PRIMES=(43,127,211,337)
N3=(147,)+(0,)*11
N1=(49,)+(0,)*11


def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def scale(a,c):
    return tuple(x*c for x in a)


def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path)
    p.add_argument('catalogue',type=Path)
    a=p.parse_args()
    pts,_,_,dirs=load_data(a.input,a.catalogue)
    centers,old=grid_neighbours(pts,dirs)
    hi=sorted(tuple(x-128 for x in q) for q,ns in centers.items()
              if q not in old and isinstance(ns,list))
    del centers,old
    n=len(hi)
    assert n==7056
    vals=[(p,*residue_maps(hi,p)) for p in PRIMES]
    count=[0]*len(vals)
    dist=0
    for i in range(n-1):
        J=np.arange(i+1,n)
        for k,(p,x,y) in enumerate(vals):
            J=J[(x[J]-x[i])*(y[J]-y[i])%p==147%p]
            count[k]+=len(J)
        for j in J.tolist():
            A,B1=hi[i],hi[j]
            d=sub(B1,A)
            if norm_numerator(d)!=N3:continue
            dist+=1
            r=mul(d,POWERS[7])
            X=add(add(scale(A,2),B1),r)
            Y=sub(add(A,scale(B1,2)),r)
            assert all(c%3==0 for c in X+Y), (i,j)
            XX=tuple(c//3 for c in X)
            YY=tuple(c//3 for c in Y)
            assert norm_numerator(sub(XX,YY))==N1
            assert all(norm_numerator(sub(Q,C))==N1 for Q in (XX,YY) for C in (A,B1))
    assert comb(n,2)==24_890_040 and dist==5691
    print(f"{comb(n,2):,} grid pairs, modular survivors {dict(zip(PRIMES,count))}.",flush=True)
    print(f"All {dist:,} exact sqrt(3)-distance pairs have both common unit centers on-grid.",flush=True)



if __name__=='__main__':
    main()
