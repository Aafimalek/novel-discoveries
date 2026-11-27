#!/usr/bin/env python3
"""Enumerate the full coefficient-lattice unit directions for denominator D."""
from collections import defaultdict
from itertools import product
from math import isqrt
from rotation_search import unit,ball,directions

def catalogue(D):
    ds = D*D
    vecs = defaultdict(list)
    for a,b,c,d in product(*(range(-isqrt(ds//weight),isqrt(ds//weight)+1)
                             for weight in [1,3,11,33])):
        a0 = a*a+3*b*b+11*c*c+33*d*d
        if a0 <= ds:
            vecs[a0, a*b+11*c*d, a*c+3*b*d, a*d+b*c].append((a,b,c,d))
    out = set()
    for (a0,a1,a2,a3), lhs in vecs.items():
        rhs = vecs.get((ds-a0,-a1,-a2,-a3),())
        out.update(a+b for a in lhs for b in rhs)
    assert all(unit(v,ds) for v in out)
    return out

if __name__=="__main__":
    p=(1,0,1,0,1,2,1,2)
    for D in [1,2,3,6,12,18,36]:
        out=catalogue(D)
        print(D,len(out),sum(not(sum(a*b for a,b in zip(v,p)) % 5) for v in out),flush=True)
