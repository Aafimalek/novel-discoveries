#!/usr/bin/env python3
"""Explicit compact typed endpoint dictionary and literal rows (no SAT solver)."""
import argparse
import itertools as I
import hashlib
from pathlib import Path

def subsets(m,k): return I.combinations(range(m),k)

def build(m,k,a,b):
    """Endpoint formula with cap max a, cup max b, heptagon size k."""
    caps, cups = (("cap",a),("cup",b))
    def pair(f,i,j,d): return (f+"Pair",d,i,j)
    def triple(f,i,j,t,d): return (f+("Last" if f=="cap" else "First"),d,i,j,t)
    def width(f,i,j,t): return (j-i if f=="cap" else t-j)+2
    def sign(x): return ("sign",*x)
    # Dictionary layout is ordered before producing IDs. Unlike the
    # generic Lean correctness theorem, execution uses an O(1) hash lookup.
    names=[sign(t) for t in subsets(m,3)]
    for f,h in (caps,cups):
        names.extend(pair(f,i,j,d) for i,j in subsets(m,2) for d in range(2,min(h,j-i+1)+1))
        names.extend(triple(f,i,j,t,d) for i,j,t in subsets(m,3) for d in range(4,min(h,width(f,i,j,t))+1))
    ids={s:i for i,s in enumerate(names,1)}
    assert len(names)==len(ids)
    def endpoint(f,i,j,t,d):
        if d==3:
            return (1 if f=="cup" else -1)*ids[sign((i,j,t))]
        return ids[triple(f,i,j,t,d)]
    def rows():
        for f,h in (caps,cups):
            for i,j in subsets(m,2):
                p=lambda d:ids[pair(f,i,j,d)]
                yield (p(2),)
                if h<=j-i+1: yield (-p(h),)
                for d in range(3,min(h,j-i+1)+1): yield (-p(d),p(d-1))
            for i,j,t in subsets(m,3):
                for d in range(3,min(h,width(f,i,j,t))+1):
                    t1=endpoint(f,i,j,t,d)
                    yield (-t1,ids[pair(f,i,t,d)])
                    if d>=h:continue
                    if f=="cap":
                        for e in range(t+1,m):
                            yield (-t1,ids[sign((j,t,e))],endpoint(f,i,t,e,d+1))
                    else:
                        for e in range(i):
                            yield (-t1,-ids[sign((e,i,j))],endpoint(f,e,i,t,d+1))
        for i,j in subsets(m,2):
            for d in range(2,k+1):
                lhs=ids.get(pair("cap",i,j,d))
                rhs=ids.get(pair("cup",i,j,k+2-d))
                if lhs is not None and rhs is not None: yield (-lhs,-rhs)
        for i,j,t,e in subsets(m,4):
            p,q,r,s=(ids[sign(t3)] for t3 in ((i,j,t),(i,j,e),(i,t,e),(j,t,e)))
            for pol in (1,-1):
                yield (-pol*p,-pol*s,pol*q)
                yield (-pol*q,-pol*s,pol*r)
                yield (-pol*p,-pol*r,pol*q)
    return names,list(rows())

def main():
    p=argparse.ArgumentParser()
    p.add_argument("m",type=int); p.add_argument("k",type=int)
    p.add_argument("cap",type=int); p.add_argument("cup",type=int)
    p.add_argument("out",type=Path)
    p.add_argument("--compare-upstream",action="store_true")
    a=p.parse_args()
    assert a.m>=3 and min(a.cap,a.cup)>=2 and a.k>=2
    names, rows=build(a.m,a.k,a.cap,a.cup)
    assert all(row and all(0<abs(l)<=len(names) for l in row) for row in rows)
    payload=("p cnf %d %d\n"%(len(names),len(rows),)
             +"".join(" ".join(map(str,row))+" 0\n" for row in rows)).encode("ascii")
    if a.compare_upstream:
        from lib.erdos import etv_signotope
        U=etv_signotope(a.k,a.cap,a.cup,a.m)
        assert U._num_vars==len(names) and len(U._clauses)==len(rows)
        assert all(tuple(up)==own for up,own in zip(U._clauses,rows))
        tail=a.out.with_suffix(".upstream.cnf")
        U.write(tail)
        assert tail.read_bytes()==payload
    a.out.write_bytes(payload)
    print(len(names),len(rows),sum(map(len,rows)),hashlib.sha256(payload).hexdigest())
if __name__=="__main__":main()
