#!/usr/bin/env python3
from itertools import combinations
from pathlib import Path
import argparse


def load_assignment(path):
    vals = {}
    for line in Path(path).read_text(encoding="ascii").splitlines():
        if line.startswith("v "):
            for fld in line.split()[1:]:
                l = int(fld)
                if l:
                    assert abs(l) not in vals or vals[abs(l)] == (l>0)
                    vals[abs(l)] = l>0
    return vals


def check(cnf, log, n, k):
    vals = load_assignment(log)
    with Path(cnf).open() as f:
        p, kind, nv, nc = f.readline().split()
        assert p == "p" and kind == "cnf"
        assert set(vals) == set(range(1,int(nv)+1))
        num = 0
        for row in f:
            *cl, zero = map(int,row.split())
            assert zero==0 and any(vals[abs(l)] == (l>0) for l in cl)
            num += 1
        assert num == int(nc)
    # Both generators assign those variables first, in the same order.
    sign = {t: vals[i] for i,t in enumerate(combinations(range(n),3),1)}
    odd = set()
    for quad in combinations(range(n),4):
        row = [sign[t] for t in combinations(quad,3)]
        assert sum(row[j] != row[j+1] for j in range(3)) <= 1
        if sum(row) % 2:
            odd.add(quad)
    checked = 0
    def check_prefix(t, nxt):
        nonlocal checked
        assert len(t)<k, f'unexpected convex-coloring {k}-set: {t}'
        prev = tuple(combinations(t, 3))
        for a in range(nxt,n):
            checked += 1
            if all(s+(a,) not in odd for s in prev):
                check_prefix(t+(a,),a+1)
    check_prefix((),0)
    print(f'{cnf}: DIMACS all {num} clauses, all packets, parity projection checked ({checked} extension nodes)')
    return sign


if __name__ == "__main__":
    p=argparse.ArgumentParser()
    p.add_argument('cnf')
    p.add_argument('log')
    p.add_argument('n',type=int)
    p.add_argument('k',type=int)
    a=p.parse_args()
    check(a.cnf,a.log,a.n,a.k)
