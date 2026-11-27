#!/usr/bin/env python3
"""Experimental one-point extensions of a concrete classical-style 32 witness.
A SAT result is only a sign assignment. UNSAT in each of the 33 insertion
slots rules out real extensions of this order type under the checked geometric
rules, not other 32-point sets. Requires only integer arithmetic for input.
"""
from argparse import ArgumentParser
from pathlib import Path
from itertools import combinations
from math import comb
from signotope_cnf import COMPACT


def determinant(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def cap_cup(k, l):
    """Extremal Pascal recursion, avoiding k+1 caps and l+1 cups."""
    if k == 1 or l == 1:
        return [(0,0)]
    A = cap_cup(k, l-1)
    B = cap_cup(k-1, l)
    dx = len(A)
    all_y = [y for x,y in A+B]
    bound = max(all_y)-min(all_y)
    dy = (len(A)+len(B))*bound + 1
    return A + [(dx+x, dy+y) for x,y in B]


def lower_witness():
    clusters = [cap_cup(k,7-k) for k in range(1,7)]
    bound = max(x+y for C in clusters for x,y in C) + 1
    L = 100 * bound**2
    return [(i*L+x, L*(i*i-20*i)+y) for i,C in enumerate(clusters) for x,y in C]


def convex_data(points):
    tris = {T: determinant(*(points[i] for i in T))
            for T in combinations(range(len(points)),3)}
    assert all(d != 0 for d in tris.values())
    sign = {T: d>0 for T,d in tris.items()}
    bad = {Q for Q in combinations(range(len(points)),4)
           if sum(sign[T] for T in combinations(Q,3)) % 2}
    assert len(points) == len(set(points))
    assert all(a[0]<b[0] for a,b in zip(points,points[1:]))
    return sign, bad


def convex_sets(n, bad):
    """Enumerate convex 6-subsets and detect any convex 7-subset."""
    hexagons = []
    def extend(s, first):
        if len(s) == 7:
            raise AssertionError("known witness failed: found " + str(s))
        if len(s) == 6:
            hexagons.append(s)
        old = list(combinations(s,3))
        for j in range(first, n):
            if not any(t+(j,) in bad for t in old):
                extend(s+(j,), j+1)
    extend((), 0)
    return hexagons


def instance(points, sign, hexagons, slot, dest):
    NEW = len(points)
    add = {T: j for j,T in enumerate(combinations(range(NEW),2),1)}
    quads = {T: j for j,T in enumerate(combinations(range(NEW),3),len(add)+1)}

    def put(clauses, ids, clause):
        mapped = []
        for lit in clause:
            x = ids[abs(lit)-1]
            if isinstance(x, bool):
                if x == (lit > 0):
                    return
            else:
                mapped.append(x if lit > 0 else -x)
        clauses.append(mapped)

    clauses = []
    order = list(range(NEW))
    order.insert(slot, NEW)
    key = {v:i for i,v in enumerate(order)}
    for T, q in quads.items():
        Q = sorted((*T,NEW), key=key.__getitem__)
        ids = [add[tuple(a for a in R if a != NEW)] if NEW in R else sign[R]
               for R in combinations(Q,3)]
        ids.append(q)
        for c in COMPACT:
            put(clauses, ids, c)
    for H in hexagons:
        clauses.append([quads[T] for T in combinations(H,3)])
    with open(dest, "w") as f:
        print(f"p cnf {len(add)+len(quads)} {len(clauses)}", file=f)
        for c in clauses:
            print(*c, 0, file=f)


def main():
    p = ArgumentParser(description=__doc__)
    p.add_argument("directory", type=Path)
    args = p.parse_args()
    args.directory.mkdir(exist_ok=True, parents=True)
    points = lower_witness()
    assert len(points)==32
    sign,bad = convex_data(points)
    hexagons = convex_sets(len(points),bad)
    print(f"{len(points)} distinct points, {len(sign)} nonzero determinants, "
          f"{len(hexagons)} convex hexagons, zero convex heptagons")
    (args.directory/"points.csv").write_text("x,y\n" + "".join(f"{x},{y}\n" for x,y in points))
    for slot in range(len(points)+1):
        instance(points,sign,hexagons,slot,args.directory/f"slot-{slot:02}.cnf")


if __name__ == "__main__":
    main()
