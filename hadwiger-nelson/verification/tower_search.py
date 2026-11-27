#!/usr/bin/env python3
"""Exact finite graph exploration in Q(sqrt(3),sqrt(5),sqrt(11))."""
import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
from math import lcm
import numpy as np
from rotation_search import colour

R=(3,5,11)
M=1<<len(R)
WEIGHTS=[1]*M
for i in range(M):
    for j,r in enumerate(R):
        if i>>j&1: WEIGHTS[i] *= r
Z=(Fraction(0),)*M
ONE=((Fraction(1),)+Z[1:],Z)
def coeff(a,i=0):
    return tuple(Fraction(a) if k==i else Fraction(0) for k in range(M))
def add(x,y):
    return tuple(a+b for a,b in zip(x,y))
def sub(x,y):
    return tuple(a-b for a,b in zip(x,y))
def mul(x,y):
    out=[Fraction(0)]*M
    for i,a in enumerate(x):
        if a:
            for j,b in enumerate(y):
                if b: out[i^j]+=a*b*WEIGHTS[i&j]
    return tuple(out)
def cmul(u,v):
    (a,b),(c,d)=u,v
    return sub(mul(a,c),mul(b,d)), add(mul(a,d),mul(b,c))
def cps(u):
    return (u[0],sub(Z,u[1])),ONE,u
def unit_directions(mixed=True):
    rho=(coeff(Fraction(1,2),1),coeff(Fraction(1,2)))
    s=(coeff(Fraction(5,6)),coeff(Fraction(1,6),4))
    t=(coeff(Fraction(2,3)),coeff(Fraction(1,3),2))
    shifts={cmul(a,b) for a,b in product(cps(s),cps(t))} if mixed else set(cps(s)+cps(t))
    moves=set()
    for p in shifts:
        for _ in range(12):
            moves.add(p[0]+p[1])
            p=cmul(p,rho)
    N=lcm(*(v.denominator for p in moves for v in p))
    moves=sorted(tuple(int(v*N) for v in p) for p in moves)
    return N,moves

def shell(moves,d):
    visited=ring={(0,)*(2*M)}
    for _ in range(d):
        ring={add(v,m) for v in ring for m in moves}-visited
        visited.update(ring)
    return sorted(visited)

def is_unit(w,N):
    dot=[0]*M
    for v in (w[:M],w[M:]):
        for i in range(M):
            for j in range(M):
                dot[i^j] += v[i]*v[j]*WEIGHTS[i&j]
    return dot==[N*N]+[0]*(M-1)

def graph(pts,N):
    # Vectors and squares are exact 64-bit integers. This guard prevents
    # overflow in both the diagonal prefilter and all mixed terms.
    mx=max(abs(z) for x in pts for z in x)
    assert max(64*max(WEIGHTS)*(2*mx)**2,N*N) < 2**63
    X=np.asarray(pts,dtype=np.int64)
    w=np.array(WEIGHTS+WEIGHTS,dtype=np.int64)
    candidates={}
    for i,p in enumerate(X):
        diff=X[i+1:]-p
        hits=np.flatnonzero((diff*diff)@w==N*N)
        for j in hits:
            d=tuple(int(z) for z in diff[j])
            ok=candidates.get(d)
            if ok is None:
                ok=candidates[d]=is_unit(d,N)
            if ok: yield i,int(j)+i+1

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--radius",type=int,default=2)
    p.add_argument("--unmixed",action="store_true")
    p.add_argument("--k",type=int,default=5)
    args=p.parse_args()
    N,moves=unit_directions(not args.unmixed)
    assert all(is_unit(v,N) for v in moves)
    pts=shell(moves,args.radius)
    print(f'N={N}, directions={len(moves)}, vertices={len(pts)}',flush=True)
    es=list(graph(pts,N))
    print(f'edges={len(es)}',flush=True)
    c=colour(len(pts),es,args.k)
    print('UNSAT not certified' if c is None else f'checked {args.k}-coloring, {sorted(Counter(c).items())}',flush=True)

if __name__=="__main__":
    main()
