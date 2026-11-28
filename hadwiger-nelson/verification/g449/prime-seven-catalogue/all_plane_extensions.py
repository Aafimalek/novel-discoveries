#!/usr/bin/env python3
"""Exact one-point extension proof with *no* grid restriction.

A point seeing all five published colors must be the circumcenter of a
triple in three fixed color classes. Modular integer filters can only
exclude triples that fail the exact radius-one identity. No float tests.
"""
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import product
from math import gcd,lcm
from pathlib import Path
import argparse,json

import numpy as np
from sympy import Poly, QQ, symbols, invert

from audit_layers import PINNED, PHI, audit, conjugate, mul, norm_numerator, parse_sparse6, sub

ZERO=(0,)*12
X=symbols("x")
MOD=Poly.from_list(list(reversed(PHI)),X,domain=QQ)

def scale(v,c):
    return tuple(x*c for x in v)

def add(a,b):
    return tuple(x+y for x,y in zip(a,b))

def scaled_rows(path):
    raw={name:(path/name).read_bytes() for name in PINNED}
    assert {k:sha256(v).hexdigest() for k,v in raw.items()}==PINNED
    rows=[tuple(map(int,r.split())) for r in raw["G449.k21"].decode().splitlines()[1:] if r]
    pts=[tuple(a//7 for a in r[:-1]) for r in rows]
    assert len(pts)==len(set(pts))==449 and all(all(a%7==0 for a in r[:-1]) for r in rows)
    n,edges=parse_sparse6(raw["G449.s6"])
    colors=[r[-1] for r in rows]
    assert n==449 and all(colors[a]!=colors[b] for a,b in edges)
    return pts,colors,edges

def roots(p):
    for s in range(2,p):
        if pow(s,42,p)==1 and all(pow(s,d,p)!=1 for d in (6,14,21)):
            t=pow(s,41,p)
            assert all(sum(c*pow(r,i,p) for i,c in enumerate(PHI))%p==0 for r in (s,t))
            return s,t
    raise ValueError("no root")

def paired_residues(pts,p):
    return tuple([sum(c*pow(r,j,p) for j,c in enumerate(a))%p for a in pts] for r in roots(p))

def triple_filter(pts,colors):
    counts=Counter(colors)
    small=sorted(counts,key=lambda a:(counts[a],a))[:3]
    classes=[[i for i,a in enumerate(colors) if a==c] for c in small]
    grid=np.array(list(product(*classes)),dtype=np.int32)
    print(f"three classes {small}; {len(grid)} triples",flush=True)
    for p in (43,127,211,337,379,463,547):
        a,b=(np.asarray(xs,dtype=np.int64) for xs in paired_residues(pts,p))
        i,j,k=grid.T
        up,um=a[j]-a[i],b[j]-b[i]
        vp,vm=a[k]-a[i],b[k]-b[i]
        U,V,W=up*um%p,vp*vm%p,(up-vp)*(um-vm)%p
        D=(up*vm-um*vp)%p
        keep=(U*V*W + 49*D*D)%p==0
        grid=grid[keep]
        print(f"mod {p}: {len(grid)}",flush=True)
    return [tuple(map(int, g)) for g in grid]

@lru_cache(maxsize=None)
def norm(a):
    return norm_numerator(a)

def exact_center(A,B,C):
    u,v=sub(B,A),sub(C,A)
    uv=mul(u,conjugate(v))
    D=sub(uv,conjugate(uv))
    if D==ZERO:
        return None
    U,V,W=norm(u),norm(v),norm(sub(B,C))
    if add(mul(mul(U,V),W),scale(mul(D,D),49))!=ZERO:
        return None
    t=sub(mul(U,v),mul(V,u))
    t=Poly.from_list(list(reversed(t)),X,domain=QQ)
    inv=invert(Poly.from_list(list(reversed(scale(D,-1))),X,domain=QQ),MOD)
    h=(t*inv).rem(MOD)
    out=[h.nth(i)+A[i] for i in range(12)]
    denominator=lcm(*(int(x.q) for x in out))
    cs=tuple(int(x*denominator) for x in out)
    assert gcd(denominator,*cs)==1
    assert all(norm(sub(cs,scale(P,denominator)))==(49*denominator**2,)+(0,)*11
               for P in (A,B,C))
    return denominator,cs

def exact_candidates(pts,colors):
    triples=triple_filter(pts,colors)
    centers={x for i,j,k in triples if (x:=exact_center(pts[i],pts[j],pts[k])) is not None}
    old=set(pts)
    print(f"{len(centers)} distinct exact centers before testing the other colors",flush=True)
    # Test every old vertex on the center's radius-one circle. Modular filters
    # precompute residues of the polynomial numerator and don't divide by d.
    results=[]
    aux=[(q,*paired_residues(pts,q),roots(q)) for q in (43,127,211)]
    for d,cs in sorted(centers):
        if d==1 and cs in old:
            continue
        ids=set(range(len(pts)))
        for p,ap,am,(r,s) in aux:
            cp=sum(c*pow(r,i,p) for i,c in enumerate(cs))%p
            cm=sum(c*pow(s,i,p) for i,c in enumerate(cs))%p
            ids={i for i in ids if ((cp-d*ap[i])*(cm-d*am[i])-49*d*d)%p==0}
        ns=sorted(i for i in ids if norm(sub(cs,scale(pts[i],d)))==(49*d*d,)+(0,)*11)
        if len({colors[i] for i in ns})==5:
            results.append((d,cs,ns))
    return results

def main():
    p=argparse.ArgumentParser()
    p.add_argument("input",type=Path)
    p.add_argument("grid_witnesses",type=Path)
    a=p.parse_args()
    audit(a.input)  # Includes exact completeness of the original sparse6 edges.
    pts,colors,edges=scaled_rows(a.input)
    result=exact_candidates(pts,colors)
    witness=json.loads(a.grid_witnesses.read_text())
    checked={(1,tuple(r["point"])):r for r in witness["single"]}
    print(f"{len(result)} outside points in the whole plane see all five original colors")
    print("scaled-coordinate denominators:",dict(Counter(d for d,_,_ in result)))
    assert {(d,cs) for d,cs,_ in result}==set(checked)
    for d,cs,ns in result:
        r=checked[d,cs]
        ys=r["colors"]
        assert ns==r["neighbors"]
        assert len(ys)==450 and set(ys)==set("01234")
        assert all(ys[i]!=ys[j] for i,j in edges) and all(ys[i]!=ys[449] for i in ns)
    print("All exact candidates have independently checked five-colorings.")

if __name__=="__main__":
    main()
