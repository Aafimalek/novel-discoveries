#!/usr/bin/env python3
"""Exact finite additive balls from 30-degree and Moser rotations.

Build the coefficientwise unit-distance graph over Q(sqrt(3),sqrt(11)),
and search for a k-colouring. A found assignment is independently checked.
A failed check / solver timeout does not establish non-colourability.
"""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import combinations
from math import lcm

R, S = 3, 11
Z = (Fraction(0),) * 4
ONE = ((Fraction(1),) + Z[1:], Z)

def q(a=0,b=0,c=0,d=0):
    return tuple(map(Fraction,(a,b,c,d)))

def add(x,y):
    return tuple(a+b for a,b in zip(x,y))

def sub(x,y):
    return tuple(a-b for a,b in zip(x,y))

def mul(x,y):
    out = [Fraction(0)] * 4
    for i, v in enumerate(x):
        for j, w in enumerate(y):
            common = i & j
            out[i ^ j] += v*w*(R if common&1 else 1)*(S if common&2 else 1)
    return tuple(out)

def cmul(u,v):
    (a,b),(c,d) = u,v
    return sub(mul(a,c),mul(b,d)),add(mul(a,d),mul(b,c))

def directions(rotations):
    rho = (q(b=Fraction(1,2)),q(a=Fraction(1,2)))
    sigma = (q(a=Fraction(5,6)),q(c=Fraction(1,6)))
    sigma_inv = (sigma[0],sub(Z,sigma[1]))
    shifts = {ONE}
    p = ONE
    for _ in range(rotations):
        p = cmul(p,sigma_inv)
    for _ in range(2*rotations+1):
        shifts.add(p)
        p = cmul(p,sigma)
    out = set()
    for p in shifts:
        for _ in range(12):
            out.add(p[0]+p[1])
            p = cmul(p,rho)
    D = lcm(*(v.denominator for p in out for v in p))
    moves = sorted(tuple(int(v*D) for v in p) for p in out)
    assert all(unit(v,D*D) for v in moves)
    return D,moves

def unit(w,scale_squared):
    a,b,c,d,e,f,g,h = w
    return (a*a+e*e+R*(b*b+f*f)+S*(c*c+g*g)+R*S*(d*d+h*h) == scale_squared
        and a*b+e*f+S*(c*d+g*h)==0
        and a*c+e*g+R*(b*d+f*h)==0
        and a*d+e*h+b*c+f*g==0)

def ball(moves,radius):
    seen = ring = {(0,)*8}
    for _ in range(radius):
        ring = {add(v,m) for v in ring for m in moves} - seen
        seen |= ring
    return sorted(seen)

def graph(pts,D):
    """Basis is independent over Q: R=3, S=11, R*S=33 nonsquares."""
    DS = D*D
    return [(i,j) for (i,v),(j,w) in combinations(enumerate(pts),2) if unit(sub(v,w), DS)]

def colour(n,edges,k):
    from pysat.solvers import Solver
    idx = lambda i,c: i*k+c+1
    formula = [[idx(i,c) for c in range(k)] for i in range(n)]
    formula.extend([-idx(i,c), -idx(j,c)] for i,j in edges for c in range(k))
    with Solver(name="cadical195",bootstrap_with=formula) as s:
        if not s.solve():
            return None
        yes = {v for v in s.get_model() if v > 0}
    out = [next(c for c in range(k) if idx(i,c) in yes) for i in range(n)]
    assert all(0 <= c < k for c in out)
    assert all(out[i]!=out[j] for i,j in edges)
    return out

def main():
    ap = ArgumentParser(description=__doc__)
    ap.add_argument("--rotations",type=int,default=1)
    ap.add_argument("--radius",type=int,default=2)
    ap.add_argument("--k",type=int,default=6)
    ap.add_argument("--output")
    args = ap.parse_args()
    if args.rotations < 0 or args.radius < 0 or args.k <= 0:
        ap.error("expected nonnegative rotations/radius and positive colour count")
    D,moves = directions(args.rotations)
    pts = ball(moves,args.radius)
    print(f"d={D}, directions={len(moves)}, vertices={len(pts)}",flush=True)
    edges = graph(pts,D)
    print(f"edges={len(edges)}",flush=True)
    colors = colour(len(pts),edges,args.k)
    print(f"{args.k}-colourable with independently checked assignment" if colors is not None
          else "solver reports UNSAT; no certificate checked",flush=True)
    if args.output:
        import json
        with open(args.output,"w",encoding="utf-8") as f:
            json.dump(dict(denominator=D,directions=moves,points=pts,edges=edges,colors=colors),f,separators=(",",":"))
            f.write("\n")

if __name__=="__main__":
    main()
