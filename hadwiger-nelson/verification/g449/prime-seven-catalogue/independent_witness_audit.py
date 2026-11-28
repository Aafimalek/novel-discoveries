#!/usr/bin/env python3
"""Second arithmetic check for all exceptional candidate-old edges."""
import argparse,json
from collections import Counter
from hashlib import sha256
from pathlib import Path
from audit_layers import PHI,PINNED,parse_sparse6


def unit(a,b):
    d=[x-y for x,y in zip(a,b)]
    c=[0]*42
    for i,x in enumerate(d):
        for j,y in enumerate(d):
            c[(i-j)%42]+=x*y
    for i in range(41,11,-1):
        if (x:=c[i])!=0:
            for j,y in enumerate(PHI):
                c[i-12+j]-=x*y
    return c[:12]==[49]+[0]*11


def main():
    p=argparse.ArgumentParser()
    p.add_argument("input",type=Path)
    p.add_argument("witnesses",type=Path)
    a=p.parse_args()
    raw={name:(a.input/name).read_bytes() for name in PINNED}
    assert {k:sha256(v).hexdigest() for k,v in raw.items()}==PINNED
    rs=[tuple(map(int,s.split())) for s in raw["G449.k21"].decode().splitlines()[1:] if s]
    pts=[tuple(x//7 for x in r[:-1]) for r in rs]
    colors=[r[-1] for r in rs]
    _,edges=parse_sparse6(raw["G449.s6"])
    cases=json.loads(a.witnesses.read_text())["single"]
    assert len(cases)==len({tuple(w["point"]) for w in cases})==34
    counts=Counter()
    for w in cases:
        x=tuple(w["point"])
        assert x not in pts
        ns=[i for i,y in enumerate(pts) if unit(x,y)]
        assert ns==w["neighbors"] and len({colors[i] for i in ns})==5
        ys=w["colors"]
        assert len(ys)==450 and set(ys)==set("01234")
        assert all(ys[i]!=ys[j] for i,j in edges) and all(ys[i]!=ys[449] for i in ns)
        counts[len(ns)]+=1
    print(f"{len(cases)*len(pts)} direct new-to-old exact comparisons.")
    print(f"All 34 colorings pass. Candidate degrees: {dict(sorted(counts.items()))}.")


if __name__=="__main__":
    main()
